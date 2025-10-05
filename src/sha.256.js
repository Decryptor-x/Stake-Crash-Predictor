/*
 * [js-sha256]{@link https://github.com/decryptor-x/Stake-Crash-Predictor}
 *
 * @version 1.1.0
 * @author Decryptor
 * @copyright Decryptor 2016-2025
 * @license MIT
 */
((function runModule() {
  'use strict';

  // messages
  var INPUT_ERR = 'input is invalid type';
  var FINAL_ERR = 'finalize already called';

  // environment probes
  var WINDOW_PRESENT = typeof window === 'object';
  var GLOBAL_CTX = WINDOW_PRESENT ? window : {};
  if (GLOBAL_CTX.JS_SHA1_NO_WINDOW) WINDOW_PRESENT = false;

  var WORKER_ENV = !WINDOW_PRESENT && typeof self === 'object';
  var NODE_ENV = !GLOBAL_CTX.JS_SHA1_NO_NODE_JS && typeof process === 'object' && process.versions && process.versions.node;
  if (NODE_ENV) GLOBAL_CTX = global;
  if (WORKER_ENV) GLOBAL_CTX = self;

  var COMMONJS = !GLOBAL_CTX.JS_SHA1_NO_COMMON_JS && typeof module === 'object' && module.exports;
  var AMD = typeof define === 'function' && define.amd;
  var HAS_AB = !GLOBAL_CTX.JS_SHA1_NO_ARRAY_BUFFER && typeof ArrayBuffer !== 'undefined';

  // lookups / tables
  var HEX_CHARS = '0123456789abcdef'.split('');
  var PAD = [-2147483648, 8388608, 32768, 128];
  var SHIFT_MAP = [24, 16, 8, 0];
  var FORMATS = ['hex', 'array', 'digest', 'arrayBuffer'];

  // safe array/view detection
  var isArrayNative = Array.isArray;
  if (GLOBAL_CTX.JS_SHA1_NO_NODE_JS || !isArrayNative) {
    isArrayNative = function (v) { return Object.prototype.toString.call(v) === '[object Array]'; };
  }

  var isABView = ArrayBuffer.isView;
  if (HAS_AB && (GLOBAL_CTX.JS_SHA1_NO_ARRAY_BUFFER_IS_VIEW || !isABView)) {
    isABView = function (v) { return typeof v === 'object' && v.buffer && v.buffer.constructor === ArrayBuffer; };
  }

  // normalize -> [value, wasString]
  function norm(v) {
    var t = typeof v;
    if (t === 'string') return [v, true];
    if (t !== 'object' || v === null) throw new Error(INPUT_ERR);
    if (HAS_AB && v.constructor === ArrayBuffer) return [new Uint8Array(v), false];
    if (!isArrayNative(v) && !isABView(v)) throw new Error(INPUT_ERR);
    return [v, false];
  }

  // --- internal state (16-word buffer + helper) ---
  function Engine(useShared) {
    if (useShared) {
      // 16 words + slot
      this.buf = new Array(17);
      for (var z = 0; z < 16; ++z) this.buf[z] = 0;
      this.buf[16] = 0;
    } else {
      this.buf = [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0];
    }

    // initial SHA-1 constants
    this.h0 = 1732584193|0;
    this.h1 = 4023233417|0;
    this.h2 = 2562383102|0;
    this.h3 = 271733878|0;
    this.h4 = 3285377520|0;

    this.block = this.start = this.bytes = this.hBytes = 0;
    this.finalized = this.hashed = false;
    this.first = true;
  }

  // update accepts string / array-like / ArrayBufferView
  Engine.prototype.update = function (input) {
    if (this.finalized) throw new Error(FINAL_ERR);

    var p = norm(input);
    input = p[0];
    var wasString = p[1];

    var idx = 0, len = input.length || 0, W = this.buf;
    var ch, i;

    while (idx < len) {
      if (this.hashed) {
        this.hashed = false;
        W[0] = this.block;
        this.block = W[16] = W[1] = W[2] = W[3] =
        W[4] = W[5] = W[6] = W[7] =
        W[8] = W[9] = W[10] = W[11] =
        W[12] = W[13] = W[14] = W[15] = 0;
      }

      if (wasString) {
        for (i = this.start; idx < len && i < 64; ++idx) {
          ch = input.charCodeAt(idx);
          if (ch < 0x80) {
            W[i >>> 2] |= ch << SHIFT_MAP[i & 3]; ++i;
          } else if (ch < 0x800) {
            W[i >>> 2] |= (0xc0 | (ch >>> 6)) << SHIFT_MAP[i & 3]; ++i;
            W[i >>> 2] |= (0x80 | (ch & 0x3f)) << SHIFT_MAP[i & 3]; ++i;
          } else if (ch < 0xD800 || ch >= 0xE000) {
            W[i >>> 2] |= (0xe0 | (ch >>> 12)) << SHIFT_MAP[i & 3]; ++i;
            W[i >>> 2] |= (0x80 | ((ch >>> 6) & 0x3f)) << SHIFT_MAP[i & 3]; ++i;
            W[i >>> 2] |= (0x80 | (ch & 0x3f)) << SHIFT_MAP[i & 3]; ++i;
          } else {
            // surrogate pair
            ch = 0x10000 + (((ch & 0x3ff) << 10) | (input.charCodeAt(++idx) & 0x3ff));
            W[i >>> 2] |= (0xf0 | (ch >>> 18)) << SHIFT_MAP[i & 3]; ++i;
            W[i >>> 2] |= (0x80 | ((ch >>> 12) & 0x3f)) << SHIFT_MAP[i & 3]; ++i;
            W[i >>> 2] |= (0x80 | ((ch >>> 6) & 0x3f)) << SHIFT_MAP[i & 3]; ++i;
            W[i >>> 2] |= (0x80 | (ch & 0x3f)) << SHIFT_MAP[i & 3]; ++i;
          }
        }
      } else {
        for (i = this.start; idx < len && i < 64; ++idx) {
          W[i >>> 2] |= input[idx] << SHIFT_MAP[i & 3]; ++i;
        }
      }

      this.lastByteIndex = i;
      this.bytes += i - this.start;

      if (i >= 64) {
        this.block = W[16];
        this.start = i - 64;
        this._processBlock();
        this.hashed = true;
      } else {
        this.start = i;
      }
    }

    if (this.bytes > 0xFFFFFFFF) {
      this.hBytes += (this.bytes / 4294967296) | 0;
      this.bytes = this.bytes % 4294967296;
    }

    return this;
  };

  Engine.prototype.finalize = function () {
    if (this.finalized) return;
    this.finalized = true;

    var W = this.buf, j = this.lastByteIndex;
    W[16] = this.block;
    W[j >>> 2] |= PAD[j & 3];
    this.block = W[16];

    if (j >= 56) {
      if (!this.hashed) this._processBlock();
      W[0] = this.block;
      W[16] = W[1] = W[2] = W[3] =
      W[4] = W[5] = W[6] = W[7] =
      W[8] = W[9] = W[10] = W[11] =
      W[12] = W[13] = W[14] = W[15] = 0;
    }

    W[14] = (this.hBytes << 3) | (this.bytes >>> 29);
    W[15] = this.bytes << 3;
    this._processBlock();
  };

  // compression / main loop
  Engine.prototype._processBlock = function () {
    var a = this.h0|0, b = this.h1|0, c = this.h2|0, d = this.h3|0, e = this.h4|0;
    var W = this.buf, t;

    for (var i = 16; i < 80; ++i) {
      t = W[i-3] ^ W[i-8] ^ W[i-14] ^ W[i-16];
      W[i] = (t << 1) | (t >>> 31);
    }

    var r = 0;
    for (; r < 20; r += 5) {
      var f = (b & c) | ((~b) & d);
      t = ((a << 5) | (a >>> 27)) + f + e + 1518500249 + (W[r] << 0);
      e = (t << 0) | 0;
      b = (b << 30) | (b >>> 2);

      f = (a & b) | ((~a) & c);
      t = ((e << 5) | (e >>> 27)) + f + d + 1518500249 + (W[r+1] << 0);
      d = (t << 0) | 0;
      a = (a << 30) | (a >>> 2);

      f = (e & a) | ((~e) & b);
      t = ((d << 5) | (d >>> 27)) + f + c + 1518500249 + (W[r+2] << 0);
      c = (t << 0) | 0;
      e = (e << 30) | (e >>> 2);

      f = (d & e) | ((~d) & a);
      t = ((c << 5) | (c >>> 27)) + f + b + 1518500249 + (W[r+3] << 0);
      b = (t << 0) | 0;
      d = (d << 30) | (d >>> 2);

      f = (c & b) | ((~c) & e);
      t = ((b << 5) | (b >>> 27)) + f + a + 1518500249 + (W[r+4] << 0);
      a = (t << 0) | 0;
      c = (c << 30) | (c >>> 2);
    }

    for (; r < 40; r += 5) {
      var ff = b ^ c ^ d;
      t = ((a << 5) | (a >>> 27)) + ff + e + 1859775393 + (W[r] << 0);
      e = (t << 0) | 0;
      b = (b << 30) | (b >>> 2);

      ff = a ^ b ^ c;
      t = ((e << 5) | (e >>> 27)) + ff + d + 1859775393 + (W[r+1] << 0);
      d = (t << 0) | 0;
      a = (a << 30) | (a >>> 2);

      ff = e ^ a ^ b;
      t = ((d << 5) | (d >>> 27)) + ff + c + 1859775393 + (W[r+2] << 0);
      c = (t << 0) | 0;
      e = (e << 30) | (e >>> 2);

      ff = d ^ e ^ a;
      t = ((c << 5) | (c >>> 27)) + ff + b + 1859775393 + (W[r+3] << 0);
      b = (t << 0) | 0;
      d = (d << 30) | (d >>> 2);

      ff = c ^ b ^ e;
      t = ((b << 5) | (b >>> 27)) + ff + a + 1859775393 + (W[r+4] << 0);
      a = (t << 0) | 0;
      c = (c << 30) | (c >>> 2);
    }

    for (; r < 60; r += 5) {
      var fff = (b & c) | (b & d) | (c & d);
      t = ((a << 5) | (a >>> 27)) + fff + e - 1894007588 + (W[r] << 0);
      e = (t << 0) | 0;
      b = (b << 30) | (b >>> 2);

      fff = (a & b) | (a & c) | (b & c);
      t = ((e << 5) | (e >>> 27)) + fff + d - 1894007588 + (W[r+1] << 0);
      d = (t << 0) | 0;
      a = (a << 30) | (a >>> 2);

      fff = (e & a) | (e & b) | (a & b);
      t = ((d << 5) | (d >>> 27)) + fff + c - 1894007588 + (W[r+2] << 0);
      c = (t << 0) | 0;
      e = (e << 30) | (e >>> 2);

      fff = (d & e) | (d & a) | (e & a);
      t = ((c << 5) | (c >>> 27)) + fff + b - 1894007588 + (W[r+3] << 0);
      b = (t << 0) | 0;
      d = (d << 30) | (d >>> 2);

      fff = (c & b) | (c & e) | (b & e);
      t = ((b << 5) | (b >>> 27)) + fff + a - 1894007588 + (W[r+4] << 0);
      a = (t << 0) | 0;
      c = (c << 30) | (c >>> 2);
    }

    for (; r < 80; r += 5) {
      var f4 = b ^ c ^ d;
      t = ((a << 5) | (a >>> 27)) + f4 + e - 899497514 + (W[r] << 0);
      e = (t << 0) | 0;
      b = (b << 30) | (b >>> 2);

      f4 = a ^ b ^ c;
      t = ((e << 5) | (e >>> 27)) + f4 + d - 899497514 + (W[r+1] << 0);
      d = (t << 0) | 0;
      a = (a << 30) | (a >>> 2);

      f4 = e ^ a ^ b;
      t = ((d << 5) | (d >>> 27)) + f4 + c - 899497514 + (W[r+2] << 0);
      c = (t << 0) | 0;
      e = (e << 30) | (e >>> 2);

      f4 = d ^ e ^ a;
      t = ((c << 5) | (c >>> 27)) + f4 + b - 899497514 + (W[r+3] << 0);
      b = (t << 0) | 0;
      d = (d << 30) | (d >>> 2);

      f4 = c ^ b ^ e;
      t = ((b << 5) | (b >>> 27)) + f4 + a - 899497514 + (W[r+4] << 0);
      a = (t << 0) | 0;
      c = (c << 30) | (c >>> 2);
    }

    this.h0 = (this.h0 + a) << 0;
    this.h1 = (this.h1 + b) << 0;
    this.h2 = (this.h2 + c) << 0;
    this.h3 = (this.h3 + d) << 0;
    this.h4 = (this.h4 + e) << 0;
  };

  // hex output
  Engine.prototype.hex = function () {
    this.finalize();
    var a = this.h0, b = this.h1, c = this.h2, d = this.h3, e = this.h4;
    return HEX_CHARS[(a >>> 28) & 0x0F] + HEX_CHARS[(a >>> 24) & 0x0F] +
           HEX_CHARS[(a >>> 20) & 0x0F] + HEX_CHARS[(a >>> 16) & 0x0F] +
           HEX_CHARS[(a >>> 12) & 0x0F] + HEX_CHARS[(a >>> 8) & 0x0F] +
           HEX_CHARS[(a >>> 4) & 0x0F] + HEX_CHARS[a & 0x0F] +
           HEX_CHARS[(b >>> 28) & 0x0F] + HEX_CHARS[(b >>> 24) & 0x0F] +
           HEX_CHARS[(b >>> 20) & 0x0F] + HEX_CHARS[(b >>> 16) & 0x0F] +
           HEX_CHARS[(b >>> 12) & 0x0F] + HEX_CHARS[(b >>> 8) & 0x0F] +
           HEX_CHARS[(b >>> 4) & 0x0F] + HEX_CHARS[b & 0x0F] +
           HEX_CHARS[(c >>> 28) & 0x0F] + HEX_CHARS[(c >>> 24) & 0x0F] +
           HEX_CHARS[(c >>> 20) & 0x0F] + HEX_CHARS[(c >>> 16) & 0x0F] +
           HEX_CHARS[(c >>> 12) & 0x0F] + HEX_CHARS[(c >>> 8) & 0x0F] +
           HEX_CHARS[(c >>> 4) & 0x0F] + HEX_CHARS[c & 0x0F] +
           HEX_CHARS[(d >>> 28) & 0x0F] + HEX_CHARS[(d >>> 24) & 0x0F] +
           HEX_CHARS[(d >>> 20) & 0x0F] + HEX_CHARS[(d >>> 16) & 0x0F] +
           HEX_CHARS[(d >>> 12) & 0x0F] + HEX_CHARS[(d >>> 8) & 0x0F] +
           HEX_CHARS[(d >>> 4) & 0x0F] + HEX_CHARS[d & 0x0F] +
           HEX_CHARS[(e >>> 28) & 0x0F] + HEX_CHARS[(e >>> 24) & 0x0F] +
           HEX_CHARS[(e >>> 20) & 0x0F] + HEX_CHARS[(e >>> 16) & 0x0F] +
           HEX_CHARS[(e >>> 12) & 0x0F] + HEX_CHARS[(e >>> 8) & 0x0F] +
           HEX_CHARS[(e >>> 4) & 0x0F] + HEX_CHARS[e & 0x0F];
  };

  Engine.prototype.toString = Engine.prototype.hex;

  // raw byte array
  Engine.prototype.digest = function () {
    this.finalize();
    var a = this.h0, b = this.h1, c = this.h2, d = this.h3, e = this.h4;
    return [
      (a >>> 24) & 0xFF, (a >>> 16) & 0xFF, (a >>> 8) & 0xFF, a & 0xFF,
      (b >>> 24) & 0xFF, (b >>> 16) & 0xFF, (b >>> 8) & 0xFF, b & 0xFF,
      (c >>> 24) & 0xFF, (c >>> 16) & 0xFF, (c >>> 8) & 0xFF, c & 0xFF,
      (d >>> 24) & 0xFF, (d >>> 16) & 0xFF, (d >>> 8) & 0xFF, d & 0xFF,
      (e >>> 24) & 0xFF, (e >>> 16) & 0xFF, (e >>> 8) & 0xFF, e & 0xFF
    ];
  };

  Engine.prototype.array = Engine.prototype.digest;

  Engine.prototype.arrayBuffer = function () {
    this.finalize();
    var ab = new ArrayBuffer(20);
    var dv = new DataView(ab);
    dv.setUint32(0, this.h0);
    dv.setUint32(4, this.h1);
    dv.setUint32(8, this.h2);
    dv.setUint32(12, this.h3);
    dv.setUint32(16, this.h4);
    return ab;
  };

  // --- HMAC wrapper ---
  function Hmac(key, useShared) {
    var pr = norm(key);
    key = pr[0];
    if (pr[1]) {
      // UTF-8 bytes from string
      var out = [], pos = 0, cc;
      for (var x = 0, L = key.length; x < L; ++x) {
        cc = key.charCodeAt(x);
        if (cc < 0x80) {
          out[pos++] = cc;
        } else if (cc < 0x800) {
          out[pos++] = 0xc0 | (cc >>> 6);
          out[pos++] = 0x80 | (cc & 0x3f);
        } else if (cc < 0xD800 || cc >= 0xE000) {
          out[pos++] = 0xe0 | (cc >>> 12);
          out[pos++] = 0x80 | ((cc >>> 6) & 0x3f);
          out[pos++] = 0x80 | (cc & 0x3f);
        } else {
          cc = 0x10000 + (((cc & 0x3ff) << 10) | (key.charCodeAt(++x) & 0x3ff));
          out[pos++] = 0xf0 | (cc >>> 18);
          out[pos++] = 0x80 | ((cc >>> 12) & 0x3f);
          out[pos++] = 0x80 | ((cc >>> 6) & 0x3f);
          out[pos++] = 0x80 | (cc & 0x3f);
        }
      }
      key = out;
    }

    if (key.length > 64) key = (new Engine(true)).update(key).array();

    var oPad = new Array(64), iPad = new Array(64);
    for (var m = 0; m < 64; ++m) {
      var kv = key[m] || 0;
      oPad[m] = 0x5c ^ kv;
      iPad[m] = 0x36 ^ kv;
    }

    Engine.call(this, useShared);
    this.update(iPad);
    this._oPad = oPad;
    this._inner = true;
    this._shared = useShared;
  }
  Hmac.prototype = new Engine();

  Hmac.prototype.finalize = function () {
    Engine.prototype.finalize.call(this);
    if (this._inner) {
      this._inner = false;
      var inner = this.array();
      Engine.call(this, this._shared);
      this.update(this._oPad);
      this.update(inner);
      Engine.prototype.finalize.call(this);
    }
  };

  // --- API factory & wiring ---
  function factory() {
    var api = function () { return new Engine(); };
    api.create = function () { return new Engine(); };
    api.update = function (m) { return api.create().update(m); };
    FORMATS.forEach(function (fmt) {
      api[fmt] = function (m) { return api.create().update(m)[fmt](); };
    });
    return api;
  }

  // Node fast path for top-level hex
  function nodeOptim(baseHex) {
    var crypto = require('crypto');
    var Buf = require('buffer').Buffer;
    var fromBuf = Buf.from && !GLOBAL_CTX.JS_SHA1_NO_BUFFER_FROM ? Buf.from : function (x) { return new Buf(x); };

    return function (inp) {
      if (typeof inp === 'string') return crypto.createHash('sha1').update(inp, 'utf8').digest('hex');
      if (inp === null || typeof inp === 'undefined') throw new Error(INPUT_ERR);
      if (inp.constructor === ArrayBuffer) inp = new Uint8Array(inp);
      if (isArrayNative(inp) || isABView(inp) || inp.constructor === Buf) {
        return crypto.createHash('sha1').update(fromBuf(inp)).digest('hex');
      }
      return baseHex(inp);
    };
  }

  // hmac creator
  function hmacFactory(format) {
    return function (key, msg) {
      return new Hmac(key, true).update(msg)[format]();
    };
  }

  var sha1 = factory();
  sha1.sha1 = sha1;

  // attach hmac helper
  (function attachH() {
    var h = hmacFactory('hex');
    h.create = function (k) { return new Hmac(k); };
    h.update = function (k, m) { return h.create(k).update(m); };
    FORMATS.forEach(function (f) { h[f] = hmacFactory(f); });
    sha1.sha1.hmac = h;
  })();

  if (NODE_ENV) {
    var optHex = nodeOptim(sha1.hex);
    sha1.create = function () { return new Engine(); };
    sha1.update = function (m) { return sha1.create().update(m); };
    sha1.hex = optHex;
    sha1.sha1 = sha1;
    sha1.sha1.hmac = sha1.sha1.hmac;
  }

  if (COMMONJS) module.exports = sha1;
  else {
    GLOBAL_CTX.sha1 = sha1;
    if (AMD) define(function () { return sha1; });
  }

}());