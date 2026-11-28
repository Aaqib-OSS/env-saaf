'use strict';
// Issue #419: seeded property-based tests for validateEnv coercion, example
// generation, min/max bounds, idempotence, and sensitive-value redaction.
// Mirrors test-scan-fuzz.js: zero dependencies, mulberry32 PRNG, and a fixed
// seed list so any failure reproduces from the seed, rule, and input printed.
//
// Generator scope stays within current main's passing contract (no silent
// catches); baseline gaps uncovered while building this suite (generateExample
// on hex `length` alone, non-https `url` `protocols` without length bounds,
// `ipv6` `minLength > 3`, `array` `unique: true` cycling, object/Date defaults
// in generateExample, and raw Date/string-json JS feedback) are tracked
// separately rather than worked around inside assertions.
const assert = require('node:assert');
const fs = require('node:fs');
const path = require('node:path');
const {
  EnvSaafError,
  generateExample,
  parseEnvFile,
  validateEnv,
  validateSchema,
} = require('./index');

const SEEDS = Array.from({ length: 320 }, (_, i) => i + 1);
const SCALAR_TYPES = [
  'string', 'number', 'int', 'boolean', 'url', 'port', 'email', 'json', 'uuid', 'jwt',
  'hex', 'ipv4', 'ipv6', 'semver', 'base64', 'date', 'file', 'duration', 'host',
];
const ALL_TYPES = [...SCALAR_TYPES, 'array'];
const STRING_TYPES = new Set([
  'string', 'email', 'url', 'file', 'uuid', 'jwt', 'hex', 'ipv4', 'ipv6', 'semver', 'base64', 'host',
]);
const SEPARATORS = [',', ';', '|'];
const FILE_FIXTURES = ['package.json', 'index.js', 'cli.js', 'LICENSE'].map((name) => (
  fs.existsSync(`./${name}`) ? `./${name}` : path.join(__dirname, name)
));
const LENGTH_RANGES = {
  string: [2, 8, 10, 28],
  hex: [2, 8, 10, 28],
  url: [12, 22, 36, 80],
  email: [18, 22, 26, 48],
  semver: [5, 10, 14, 32],
  host: [4, 9, 24, 60],
};

/** mulberry32: tiny, deterministic PRNG matching test-scan-fuzz.js. */
function rng(seed) {
  let a = seed >>> 0;
  return () => {
    a = (a + 0x6D2B79F5) >>> 0;
    let t = a;
    t = Math.imul(t ^ (t >>> 15), t | 1);
    t ^= t + Math.imul(t ^ (t >>> 7), t | 61);
    return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
  };
}

const pick = (random, list) => list[Math.floor(random() * list.length)];
const intBetween = (random, lo, hi) => lo + Math.floor(random() * (hi - lo + 1));

function charsFrom(random, alphabet, len) {
  let out = '';
  for (let i = 0; i < len; i++) out += alphabet[intBetween(random, 0, alphabet.length - 1)];
  return out;
}
const hexString = (random, len) => charsFrom(random, '0123456789abcdefABCDEF', len);
const alphaNum = (random, len) => charsFrom(random, 'abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789', len);
const isoDateAt = (days) => new Date(Date.UTC(2025, 0, 1) + days * 86400000).toISOString().slice(0, 10);
const durationMsOf = (b) => (typeof b === 'number' ? b : validateEnv({ D: { type: 'duration' } }, { D: b }).D);

function withUnderscore(n, random) {
  if (!Number.isInteger(n) || Math.abs(n) < 1000 || random() >= 0.35) return String(n);
  const digits = String(Math.abs(n));
  return `${n < 0 ? '-' : ''}${digits[0]}_${digits.slice(1)}`;
}

/** Generate a valid synthetic scalar string for `type` respecting `rule`. */
function validScalarRaw(random, type, rule, forArrayItem = false) {
  if (Array.isArray(rule.choices) && rule.choices.length > 0) return String(pick(random, rule.choices));
  switch (type) {
    case 'string': {
      const lo = Math.max(1, rule.minLength ?? 1);
      const hi = Math.min(rule.maxLength ?? 24, Math.max(lo, 24));
      if (rule.pattern) return `app_${alphaNum(random, Math.max(2, lo))}`;
      const core = alphaNum(random, intBetween(random, lo, hi));
      return !forArrayItem && rule.trim !== false && random() < 0.3 ? `  ${core}  ` : core;
    }
    case 'number': {
      const lo = rule.min ?? -5000;
      const hi = rule.max ?? 5000;
      const val = lo === hi ? lo : Math.min(hi, Math.max(lo, Number((lo + random() * (hi - lo)).toFixed(2))));
      return withUnderscore(val, random);
    }
    case 'int':
      return withUnderscore(intBetween(random, rule.min ?? -2000, rule.max ?? 2000), random);
    case 'port':
      return String(intBetween(random, rule.min ?? 0, rule.max ?? 65535));
    case 'duration': {
      const lo = rule.min !== undefined ? durationMsOf(rule.min) : 0;
      const hi = rule.max !== undefined ? durationMsOf(rule.max) : 7200000;
      const ms = intBetween(random, Math.ceil(lo / 1000), Math.floor(hi / 1000)) * 1000;
      if (ms > 0 && ms % 60000 === 0 && random() < 0.5) return `${ms / 60000}m`;
      return ms >= 1000 && random() < 0.7 ? `${ms / 1000}s` : `${ms}ms`;
    }
    case 'boolean':
      return pick(random, ['true', 'false', '1', '0', 'yes', 'no', 'on', 'off', 'y', 'n', ' TRUE ', 'Off']);
    case 'url': {
      const schemes = Array.isArray(rule.protocols) && rule.protocols.length
        ? rule.protocols.map((p) => p.replace(/:$/, '').toLowerCase())
        : ['https', 'http'];
      const base = `${pick(random, schemes)}://svc-${intBetween(random, 1, 99)}.example.com/v1`;
      const lo = rule.minLength ?? 0;
      return (base.length < lo ? `${base}/${'a'.repeat(lo - base.length - 1)}` : base).slice(0, rule.maxLength ?? 120);
    }
    case 'email': {
      const domain = '@app.example.com';
      const lo = Math.max(1, (rule.minLength ?? 6) - domain.length);
      const hi = Math.max(lo, Math.min(16, (rule.maxLength ?? 48) - domain.length));
      return `${alphaNum(random, intBetween(random, lo, hi)).toLowerCase()}${domain}`;
    }
    case 'json':
      if (forArrayItem) {
        return pick(random, [`{"k":${intBetween(random, 1, 99)}}`, `[${intBetween(random, 1, 9)}]`, `"v_${alphaNum(random, 4)}"`, '42', 'true']);
      }
      if (rule.min !== undefined || rule.max !== undefined) return String(intBetween(random, rule.min ?? 0, rule.max ?? 100));
      return pick(random, [`{"ok":true,"n":${intBetween(random, 1, 99)}}`, `["${alphaNum(random, 4)}",1]`, `"str_${alphaNum(random, 5)}"`, 'null', 'false']);
    case 'uuid':
      return [8, 4, 4, 4, 12].map((n) => hexString(random, n)).join('-');
    case 'jwt': {
      // A well-formed token: header and payload are JSON objects, the
      // signature is any non-empty base64url string (never verified).
      const b64u = (o) => Buffer.from(JSON.stringify(o)).toString('base64url');
      return `${b64u({ alg: 'HS256', typ: 'JWT' })}.${b64u({ sub: String(intBetween(random, 1, 99999)), iat: 1700000000 })}.${alphaNum(random, 43)}`;
    }
    case 'hex': {
      const lo = rule.length ?? Math.max(2, rule.minLength ?? 2);
      const hi = rule.length ?? Math.max(lo, Math.min(32, rule.maxLength ?? 24));
      return hexString(random, intBetween(random, lo, hi));
    }
    case 'ipv4':
      return `${intBetween(random, 1, 223)}.${intBetween(random, 0, 255)}.${intBetween(random, 0, 255)}.${intBetween(random, 1, 254)}`;
    case 'ipv6':
      return pick(random, ['::1', `2001:db8::${intBetween(random, 1, 999).toString(16)}`, 'fe80::1%eth0', '::ffff:192.0.2.1']);
    case 'semver': {
      const base = `${random() < 0.3 ? 'v' : ''}${intBetween(random, 0, 9)}.${intBetween(random, 0, 20)}.${intBetween(random, 0, 30)}`;
      const lo = rule.minLength ?? 0;
      return base.length < lo ? `${base}+${alphaNum(random, Math.max(1, lo - base.length - 1))}` : base;
    }
    case 'base64': {
      const urlSafe = random() < 0.4;
      const chars = `ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789${urlSafe ? '-_' : '+/'}`;
      const groups = Math.max(1, Math.min(Math.floor((rule.maxLength ?? 24) / 4), Math.ceil((rule.minLength ?? 4) / 4)));
      const pad = !urlSafe && random() < 0.5 ? pick(random, [0, 1, 2]) : 0;
      return charsFrom(random, chars, groups * 4 - pad) + '='.repeat(pad);
    }
    case 'date': {
      const loDay = rule.min ? Math.round((Date.parse(rule.min) - Date.UTC(2025, 0, 1)) / 86400000) : -365;
      const hiDay = rule.max ? Math.round((Date.parse(rule.max) - Date.UTC(2025, 0, 1)) / 86400000) : 730;
      const day = isoDateAt(intBetween(random, loDay, hiDay));
      return random() < 0.4 && day !== rule.max ? `${day}T12:30:00Z` : day;
    }
    case 'file':
      return pick(random, FILE_FIXTURES);
    case 'host': {
      const base = pick(random, [`db-${intBetween(random, 1, 99)}.internal`, `api-${intBetween(random, 1, 99)}.example.com.`, 'localhost', '10.0.0.5']);
      const lo = rule.minLength ?? 0;
      return base.length < lo ? `svc-${'a'.repeat(lo - 4)}.internal` : base;
    }
    default:
      throw new Error(`unhandled scalar type: ${type}`);
  }
}

function scalarBadRaw(random, type, rule, tag) {
  if (type === 'string') {
    if (rule.pattern) return `nope_${tag}`;
    if (rule.choices) return `outside_${tag}`;
    if (rule.maxLength !== undefined) return `${tag}_${'x'.repeat(rule.maxLength + 4)}`;
    return (rule.minLength ?? 0) >= 8 ? tag.slice(0, 6) : null;
  }
  if (type === 'number' && rule.max !== undefined && random() < 0.5) return `${Math.trunc(rule.max) + 948271}.37`;
  if (type === 'int' && rule.max !== undefined && random() < 0.5) return String(rule.max + 948271);
  if (type === 'port' && random() < 0.5) return '794821';
  if (type === 'duration' && rule.max !== undefined && random() < 0.5) return `${Math.trunc(durationMsOf(rule.max)) + 948271}ms`;
  if (type === 'url' && Array.isArray(rule.protocols) && !rule.protocols.includes('ftp') && random() < 0.5) return `ftp://${tag}.example.com/r`;
  if (type === 'hex' && rule.length !== undefined && random() < 0.5) return 'deadbeefcafe0123456789abcdef012345';
  if (type === 'date' && rule.max !== undefined && random() < 0.5) return '2189-11-23';
  const malformed = {
    number: `nan_${tag}`, int: `12.5_${tag}`, port: `port_${tag}`, duration: `15bad_${tag}`,
    boolean: `maybe_${tag}`, url: `not_a_url_${tag}`, email: `invalid_email_${tag}`,
    json: `{broken_${tag}`, uuid: `not-uuid-${tag}`, jwt: `not-a-jwt-${tag}`, hex: `0x_${tag}`, ipv4: `999.1.1.${tag}`,
    ipv6: `gggg::${tag}`, semver: `V01.2.${tag}`, base64: `bad!b64!${tag}=`,
    date: `2026-02-30-${tag}`, file: `./__missing_${tag}.json`, host: `https://${tag}.example.com:8080/p`,
  };
  return malformed[type] || `bad_${tag}`;
}

/** Generate a valid rule for `type` alongside valid and invalid synthetic values. */
function generateCase(random, type, seed, index) {
  const key = `V${seed}_${index}_CFG`;
  const tag = `sec${seed}k${index}z9`;
  const rule = { type };
  if (random() < 0.25) rule.description = `Synthetic rule ${seed}-${index}`;
  if (random() < 0.2) rule.deprecated = random() < 0.5 ? true : `Use NEXT_${key}`;
  if (random() < 0.2) rule.aliases = [`OLD_${key}`];

  if (type === 'array') {
    const of = SCALAR_TYPES[(seed + index) % SCALAR_TYPES.length];
    rule.of = of;
    if (random() < 0.6) rule.separator = pick(random, SEPARATORS);
    if (random() < 0.35) rule.skipEmpty = true;
    const unique = of !== 'file' && random() < 0.35;
    if (unique) rule.unique = true;

    const maxCap = unique ? (of === 'boolean' ? 2 : 3) : 5;
    if (random() < 0.55) {
      const minItems = intBetween(random, 1, Math.min(2, maxCap));
      const maxItems = intBetween(random, minItems, maxCap);
      if (random() < 0.7) rule.minItems = minItems;
      if (random() < 0.7 || (unique && of === 'boolean')) rule.maxItems = maxItems;
    } else if (unique && of === 'boolean') {
      rule.maxItems = 2;
    }
    if (of === 'url' && random() < 0.4) rule.protocols = ['https', 'http'];

    if (!['date', 'json', 'duration', 'file'].includes(of) && random() < 0.25) {
      const sample = { type: of, protocols: rule.protocols };
      const distinct = [...new Set([0, 1].map(() => (
        validateEnv({ C: sample }, { C: validScalarRaw(random, of, sample, true) }, { onWarn: () => {} }).C
      )))];
      if (!unique || distinct.length >= (rule.minItems ?? 1)) rule.choices = distinct;
    }

    const sep = rule.separator || ',';
    const loCount = rule.minItems ?? 1;
    const hiCount = rule.maxItems ?? Math.max(loCount, 3);
    const targetCount = rule.choices && unique
      ? Math.min(hiCount, Math.max(loCount, 1), rule.choices.length)
      : intBetween(random, loCount, hiCount);

    const items = [];
    const seen = new Set();
    for (let guard = 0; items.length < targetCount && guard < 40; guard++) {
      const itemRule = { type: of, protocols: rule.protocols, choices: rule.choices };
      const raw = validScalarRaw(random, of, itemRule, true);
      const coerced = validateEnv({ I: itemRule }, { I: raw }, { onWarn: () => {} }).I;
      const token = coerced !== null && typeof coerced === 'object' ? JSON.stringify(coerced) : coerced;
      if (unique && seen.has(token)) continue;
      seen.add(token);
      items.push(raw);
    }
    const goodRaw = rule.skipEmpty && random() < 0.5 ? `${sep}${items.join(sep + sep)}${sep}` : items.join(sep);
    if (random() < 0.2) rule.default = items.join(sep);

    let badRaw = null;
    if (!rule.skipEmpty && random() < 0.25) badRaw = `${tag}_a${sep}${sep}${tag}_b`;
    else if (unique && (loCount <= 2) && (rule.maxItems ?? 9) >= 2 && of === 'string' && !rule.choices) badRaw = `${tag}_d${sep}${tag}_d`;
    else if (of === 'string' && rule.choices) badRaw = `${tag}_outside`;
    else if (of === 'string' && !rule.skipEmpty) badRaw = `${tag}_item${sep}`;
    else if (of !== 'string') badRaw = scalarBadRaw(random, of, rule, tag);

    const quotedDefault = typeof rule.default === 'string' && rule.default.startsWith('"');
    const canCheckExample = of !== 'file' && !quotedDefault
      && !(unique && of === 'boolean' && !rule.choices && (rule.maxItems ?? 3) > 2);
    return { key, rule, goodRaw, badRaw, tag, canCheckExample };
  }

  if (['number', 'int', 'port', 'duration'].includes(type)) {
    if (random() < 0.65) {
      if (type === 'duration') {
        const lo = intBetween(random, 1, 1800);
        const hi = intBetween(random, lo, 7200);
        if (random() < 0.8) rule.min = random() < 0.5 ? lo * 1000 : `${lo}s`;
        if (random() < 0.8) rule.max = random() < 0.5 ? hi * 1000 : `${hi}s`;
      } else {
        const [floor, mid, ceil] = type === 'port' ? [0, 40000, 65535] : [-800, 400, 1600];
        const lo = intBetween(random, floor, mid);
        const hi = intBetween(random, lo, ceil);
        if (random() < 0.8) rule.min = lo;
        if (random() < 0.8) rule.max = hi;
      }
    }
    if (random() < 0.25) {
      rule.choices = [...new Set([0, 1].map(() => (
        validateEnv({ C: rule }, { C: validScalarRaw(random, type, rule) }, { onWarn: () => {} }).C
      )))];
    }
  } else if (type === 'date' && random() < 0.65) {
    const d1 = intBetween(random, -200, 200);
    const d2 = intBetween(random, d1, 500);
    if (random() < 0.8) rule.min = isoDateAt(d1);
    if (random() < 0.8) rule.max = isoDateAt(d2);
  } else if (STRING_TYPES.has(type)) {
    if (type === 'url' && random() < 0.5) rule.protocols = pick(random, [['https'], ['https', 'http'], ['ws', 'wss']]);
    if (type === 'hex' && random() < 0.45) rule.length = pick(random, [4, 8, 16, 32]);
    if (!['uuid', 'jwt', 'ipv4', 'ipv6', 'file'].includes(type) && random() < 0.45) {
      if (type === 'hex' && rule.length !== undefined) {
        rule.minLength = Math.max(1, rule.length - 2);
        rule.maxLength = rule.length + 4;
      } else if (type === 'base64') {
        rule.minLength = pick(random, [4, 8]);
        rule.maxLength = pick(random, [16, 24]);
      } else {
        const [minLo, minHi, maxLo, maxHi] = LENGTH_RANGES[type];
        rule.minLength = intBetween(random, minLo, minHi);
        rule.maxLength = intBetween(random, Math.max(rule.minLength, maxLo), maxHi);
      }
    }
    if (type === 'string' && random() < 0.35) {
      rule.pattern = random() < 0.5 ? '^app_[A-Za-z0-9]+$' : /^app_[A-Za-z0-9]+$/;
      rule.trim = true;
    } else if (type === 'string' && random() < 0.25) {
      rule.trim = false;
    }
    if (!rule.pattern && type !== 'file' && random() < 0.25) {
      rule.choices = [...new Set([0, 1].map(() => validScalarRaw(random, type, { ...rule, trim: true }).trim()))];
    }
  } else if (type === 'boolean' && random() < 0.3) {
    rule.choices = pick(random, [[true], [false], [true, false]]);
  } else if (type === 'json' && random() < 0.35) {
    rule.min = 10;
    rule.max = 90;
  }

  if (['hex', 'uuid', 'email', 'host'].includes(type) && !rule.choices && random() < 0.25) {
    rule.transform = (v) => v.toLowerCase();
  }
  const goodRaw = validScalarRaw(random, type, rule);
  if (type !== 'file' && random() < 0.2) rule.default = goodRaw.trim();
  const badRaw = scalarBadRaw(random, type, rule, tag);

  const urlNoHttpsOrLen = type === 'url' && Array.isArray(rule.protocols)
    && !rule.protocols.some((p) => p.replace(/:$/, '').toLowerCase() === 'https')
    && rule.minLength === undefined && rule.maxLength === undefined && rule.default === undefined && !rule.choices;
  const hexLengthAlone = type === 'hex' && rule.length !== undefined && rule.length !== 8
    && rule.minLength === undefined && rule.maxLength === undefined && rule.default === undefined && !rule.choices;
  const unseededPattern = Boolean(rule.pattern) && rule.default === undefined && !rule.choices;
  const quotedDefault = typeof rule.default === 'string' && rule.default.startsWith('"');
  const canCheckExample = type !== 'file' && !urlNoHttpsOrLen && !hexLengthAlone && !unseededPattern && !quotedDefault;
  return { key, rule, goodRaw, badRaw, tag, canCheckExample };
}

function serializeScalar(type, val) {
  if (type === 'date') return val.toISOString();
  return type === 'json' ? JSON.stringify(val) : String(val);
}

function serializeForEnv(rule, val) {
  if ((rule.type || 'string') !== 'array') return serializeScalar(rule.type || 'string', val);
  return val.map((item) => serializeScalar(rule.of || 'string', item)).join(rule.separator || ',');
}

function assertSameCoerced(actual, expected, context) {
  if (expected instanceof Date) {
    assert.ok(actual instanceof Date && actual.getTime() === expected.getTime(), `Date drifted on re-validation\n${context}`);
    return;
  }
  assert.deepStrictEqual(actual, expected, `coerced value changed on re-validation\n${context}`);
}

function assertWithinBounds(rule, val, context) {
  const type = rule.type || 'string';
  if (['number', 'int', 'port', 'duration'].includes(type) && typeof val === 'number') {
    if (rule.min !== undefined) assert.ok(val >= durationMsOf(rule.min), `value ${val} < min ${rule.min}\n${context}`);
    if (rule.max !== undefined) assert.ok(val <= durationMsOf(rule.max), `value ${val} > max ${rule.max}\n${context}`);
  } else if (type === 'date' && val instanceof Date) {
    if (rule.min !== undefined) assert.ok(val.getTime() >= Date.parse(rule.min), `date ${val.toISOString()} < min ${rule.min}\n${context}`);
    if (rule.max !== undefined) assert.ok(val.getTime() <= Date.parse(rule.max), `date ${val.toISOString()} > max ${rule.max}\n${context}`);
  }
}

const formatRule = (rule) => JSON.stringify(rule, (_k, v) => (
  v instanceof RegExp ? v.toString() : typeof v === 'function' ? '[Function]' : v
));

function withDetail(step, detail, fn) {
  try {
    return fn();
  } catch (err) {
    if (err instanceof assert.AssertionError && String(err.message).includes('seed ')) throw err;
    assert.fail(`[${step}] ${err && err.message ? err.message : String(err)}\n${detail}`);
  }
}

const seenTypes = new Set();
const seenArrayItemTypes = new Set();
let rulesChecked = 0;
let examplesChecked = 0;
let boundedBothChecked = 0;
let sensitiveErrorsChecked = 0;

function runSeed(seed) {
  const random = rng(seed);
  const perSeed = 2 + Math.floor(random() * 3);
  const batchCases = [];
  for (let i = 0; i < perSeed; i++) {
    const type = ALL_TYPES[(seed * 3 + i) % ALL_TYPES.length];
    const generated = withDetail('generateCase', `seed ${seed} (case ${i}, type: ${type})`, () => generateCase(random, type, seed, i));
    batchCases.push(generated);
  }
  return { random, batchCases };
}

// Seeded replay check: the same seed always produces identical rules and inputs.
assert.deepStrictEqual(
  JSON.stringify(runSeed(17).batchCases.map((c) => [c.key, formatRule(c.rule), c.goodRaw, c.badRaw])),
  JSON.stringify(runSeed(17).batchCases.map((c) => [c.key, formatRule(c.rule), c.goodRaw, c.badRaw])),
  'seed 17 generator replay differed',
);

for (const seed of SEEDS) {
  const { random, batchCases } = runSeed(seed);
  for (let i = 0; i < batchCases.length; i++) {
    const { key, rule, goodRaw, badRaw, tag, canCheckExample } = batchCases[i];
    const type = rule.type;
    seenTypes.add(type);
    if (type === 'array') seenArrayItemTypes.add(rule.of);
    rulesChecked++;

    const schema = { [key]: rule };
    const baseCtx = `seed ${seed} (case ${i})\nkey: ${key}\nrule: ${formatRule(rule)}`;

    // 1. Valid schema + valid synthetic input.
    const accepted = withDetail('accept-valid', `${baseCtx}\ninput: ${JSON.stringify(goodRaw)}`, () => {
      validateSchema(schema);
      return validateEnv(schema, { [key]: goodRaw }, { onWarn: () => {} });
    });
    assert.ok(Object.isFrozen(accepted) && Object.prototype.hasOwnProperty.call(accepted, key), `missing/unfrozen result\n${baseCtx}`);
    const firstVal = accepted[key];
    assertWithinBounds(rule, firstVal, `${baseCtx}\ninput: ${JSON.stringify(goodRaw)}`);

    // 2. Idempotence: feeding the accepted value back through the same rule succeeds and matches.
    const reencoded = serializeForEnv(rule, firstVal);
    const secondEnv = withDetail('idempotence-env-string', `${baseCtx}\nreencoded: ${JSON.stringify(reencoded)}`, () => (
      validateEnv(schema, { [key]: reencoded }, { onWarn: () => {} })
    ));
    assertSameCoerced(secondEnv[key], firstVal, `${baseCtx}\nreencoded: ${JSON.stringify(reencoded)}`);

    const supportsDirectJs = type !== 'date'
      && !(type === 'json' && (firstVal === null || typeof firstVal === 'string'))
      && !(type === 'array' && rule.of === 'json' && firstVal.some((v) => v === null || typeof v === 'string'))
      && !(typeof firstVal === 'string' && firstVal === '');
    if (supportsDirectJs) {
      const directAgain = withDetail('idempotence-direct-js', `${baseCtx}\ndirectJsInput: ${JSON.stringify(firstVal)}`, () => (
        validateEnv(schema, { [key]: firstVal }, { onWarn: () => {} })
      ));
      assertSameCoerced(directAgain[key], firstVal, `${baseCtx}\ndirectJsInput: ${JSON.stringify(firstVal)}`);
    }

    // 3. Generated .env.example validates against its rule and honours min/max bounds.
    if (canCheckExample) {
      const exampleText = generateExample(schema);
      const exCtx = `${baseCtx}\nexample:\n${exampleText}`;
      const fromExample = withDetail('example-roundtrip', exCtx, () => {
        const exampleSchema = { [key]: rule.default === undefined ? { ...rule, required: true } : rule };
        const res = validateEnv(exampleSchema, parseEnvFile(exampleText), { onWarn: () => {} });
        const again = validateEnv(exampleSchema, { [key]: serializeForEnv(rule, res[key]) }, { onWarn: () => {} });
        assertSameCoerced(again[key], res[key], exCtx);
        return res;
      });
      assertWithinBounds(rule, fromExample[key], exCtx);
      if (rule.min !== undefined && rule.max !== undefined) boundedBothChecked++;
      examplesChecked++;
    }

    // 4. Missing required key always names the key.
    if (rule.default === undefined) {
      let missingErr;
      assert.throws(
        () => validateEnv({ [key]: { ...rule, required: true, sensitive: true } }, {}, { onWarn: () => {} }),
        (err) => { missingErr = err; return err instanceof EnvSaafError; },
        `missing required key did not throw\n${baseCtx}`,
      );
      assert.ok(missingErr.message.includes(key) && missingErr.errors.every((e) => e.startsWith(`${key}: `)), `missing error omitted ${key}\n${baseCtx}`);
    }

    // 5. Invalid value names the key, matches { throwOnError: false }, and never leaks a sensitive raw value.
    const { default: _omittedDefault, ...ruleWithoutDefault } = rule;
    const checkRule = badRaw !== null
      ? { ...rule, sensitive: true }
      : { ...ruleWithoutDefault, choices: ['allowed_only'], sensitive: true };
    const rawSecret = badRaw !== null ? badRaw : `nope_${tag}`;
    const sensSchema = { [key]: checkRule };
    const errCtx = `${baseCtx}\nsensitiveRule: ${formatRule(checkRule)}\nbadInput: ${JSON.stringify(rawSecret)}`;

    let thrown;
    assert.throws(
      () => validateEnv(sensSchema, { [key]: rawSecret }, { onWarn: () => {} }),
      (err) => { thrown = err; return err instanceof EnvSaafError; },
      `invalid input did not throw EnvSaafError\n${errCtx}`,
    );
    assert.ok(thrown.errors.length >= 1 && thrown.message.includes(key), `thrown error omitted ${key}\n${errCtx}`);
    assert.ok(!thrown.message.includes(rawSecret), `sensitive raw value leaked in error.message\n${errCtx}`);
    for (const entry of thrown.errors) {
      assert.ok(entry.startsWith(`${key}: `) || entry.startsWith(`${key}[`), `error omitted ${key}: ${entry}\n${errCtx}`);
      assert.ok(!entry.includes(rawSecret), `sensitive raw value leaked in errors: ${entry}\n${errCtx}`);
    }
    for (const detail of thrown.details) {
      assert.ok(detail.key === key || detail.key.startsWith(`${key}[`), `detail.key mismatch: ${JSON.stringify(detail)}\n${errCtx}`);
      assert.ok(!detail.message.includes(rawSecret), `sensitive raw value leaked in details: ${JSON.stringify(detail)}\n${errCtx}`);
    }

    const collected = validateEnv(sensSchema, { [key]: rawSecret }, { throwOnError: false, onWarn: () => {} });
    assert.deepStrictEqual(collected.errors, thrown.errors, `throwOnError:false errors diverged\n${errCtx}`);
    assert.deepStrictEqual(collected.details, thrown.details, `throwOnError:false details diverged\n${errCtx}`);
    assert.ok(!Object.prototype.hasOwnProperty.call(collected.env, key), `failed key ${key} present in env\n${errCtx}`);
    sensitiveErrorsChecked++;
  }

  // 6. Multi-key + grouped schema composition and determinism.
  const [first, ...rest] = batchCases;
  const groupPrefix = `GRP${seed}_`;
  const multiSchema = { GRP: { prefix: groupPrefix, schema: { [first.key]: first.rule } } };
  const multiEnv = { [`${groupPrefix}${first.key}`]: first.goodRaw };
  const badItems = [];
  for (const item of rest) {
    if (item.badRaw !== null && random() < 0.5) {
      multiSchema[item.key] = { ...item.rule, sensitive: true };
      multiEnv[item.key] = item.badRaw;
      badItems.push(item);
    } else {
      multiSchema[item.key] = item.rule;
      multiEnv[item.key] = item.goodRaw;
    }
  }
  const runA = validateEnv(multiSchema, multiEnv, { throwOnError: false, onWarn: () => {} });
  const runB = validateEnv(multiSchema, multiEnv, { throwOnError: false, onWarn: () => {} });
  assert.ok(Object.isFrozen(runA.env) && Object.isFrozen(runA.env.GRP), `seed ${seed} grouped result not frozen`);
  assert.deepStrictEqual(runA.errors, runB.errors, `seed ${seed} repeated errors differed`);
  assert.deepStrictEqual(runA.details, runB.details, `seed ${seed} repeated details differed`);
  for (const bad of badItems) {
    assert.ok(runA.errors.some((e) => e.startsWith(`${bad.key}: `) || e.startsWith(`${bad.key}[`)), `seed ${seed} missed ${bad.key}`);
    assert.ok(runA.errors.every((e) => !e.includes(bad.badRaw)), `seed ${seed} leaked ${bad.key}`);
  }
}

assert.deepStrictEqual([...seenTypes].sort(), [...ALL_TYPES].sort(), 'not all env-saaf types were exercised');
assert.deepStrictEqual([...seenArrayItemTypes].sort(), [...SCALAR_TYPES].sort(), 'not all array `of` scalar types were exercised');
assert.ok(boundedBothChecked >= 40, `expected min+max example checks, saw ${boundedBothChecked}`);

console.log(
  `test-validate-fuzz.js: ${SEEDS.length} seeds, ${rulesChecked} rules (${ALL_TYPES.length} types), `
  + `${examplesChecked} examples (${boundedBothChecked} min/max bounded), ${sensitiveErrorsChecked} sensitive checks, all invariants held`,
);
