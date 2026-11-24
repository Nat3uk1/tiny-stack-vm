// A tiny stack VM for make.fun's tiny stack ISA v1: an exact interpreter of the reference semantics.
// For every instance in the input dir it writes stdout.bin (the bytes the program wrote) and exit.txt
// (its exit code: 0 on HALT, the EXIT value's low byte, or a trap's code). Plain JavaScript, Node built-ins only.
import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';

// Per-opcode tables: immediate length (-1 = unknown opcode), values popped, values pushed.
const IMM = new Int8Array(256).fill(-1);
const POP = new Int8Array(256);
const PSH = new Int8Array(256);
function def(b, i, p, q) { IMM[b] = i; POP[b] = p; PSH[b] = q; }
def(0x00, 0, 0, 0); // HALT
def(0x01, 1, 0, 1); // PUSH8
def(0x02, 4, 0, 1); // PUSH32
def(0x03, 0, 1, 0); // POP
def(0x04, 0, 1, 2); // DUP
def(0x05, 0, 2, 2); // SWAP
def(0x06, 0, 2, 3); // OVER
def(0x07, 0, 3, 3); // ROT
for (const b of [0x10, 0x11, 0x12, 0x13, 0x14, 0x15, 0x16, 0x18, 0x19, 0x1a, 0x1c, 0x1d, 0x1e, 0x20, 0x21, 0x22]) def(b, 0, 2, 1);
def(0x17, 0, 1, 1); // NEG
def(0x1b, 0, 1, 1); // NOT
def(0x30, 2, 0, 0); // JMP
def(0x31, 2, 1, 0); // JZ
def(0x32, 2, 1, 0); // JNZ
def(0x33, 2, 0, 0); // CALL
def(0x34, 0, 0, 0); // RET
def(0x40, 0, 1, 1); // LOAD
def(0x41, 0, 2, 0); // STORE
def(0x50, 0, 1, 0); // PRINT
def(0x51, 0, 1, 0); // PUTC
def(0x52, 0, 0, 1); // IN
def(0x53, 0, 1, 0); // EXIT

const OUT_MAX = 65536;

// Runs one program to its end; returns [output bytes, exit code].
function run(P, I) {
  const n = P.length;
  const D = new Int32Array(256);
  const C = new Int32Array(64);
  const M = new Int32Array(256);
  const out = new Uint8Array(OUT_MAX);
  let sp = 0, csp = 0, olen = 0, ip = 0, pc = 0, steps = 0;
  const done = (code) => [out.slice(0, olen), code];
  for (;;) {
    if (steps === 1000000) return done(10); // step limit
    if (pc < 0 || pc >= n) return done(9); // pc outside the program
    const op = P[pc];
    const im = IMM[op];
    if (im < 0) return done(5); // unknown opcode
    if (pc + im >= n) return done(9); // immediate cut off by the program's end
    steps++;
    if (sp < POP[op]) return done(2); // stack underflow
    if (sp - POP[op] + PSH[op] > 256) return done(3); // stack overflow
    const next = pc + 1 + im;
    pc = next;
    switch (op) {
      case 0x00: return done(0); // HALT
      case 0x01: D[sp++] = (P[next - 1] << 24) >> 24; break; // PUSH8, sign-extended
      case 0x02: D[sp++] = P[next - 4] | (P[next - 3] << 8) | (P[next - 2] << 16) | (P[next - 1] << 24); break; // PUSH32
      case 0x03: sp--; break; // POP
      case 0x04: D[sp] = D[sp - 1]; sp++; break; // DUP
      case 0x05: { const t = D[sp - 1]; D[sp - 1] = D[sp - 2]; D[sp - 2] = t; break; } // SWAP
      case 0x06: D[sp] = D[sp - 2]; sp++; break; // OVER
      case 0x07: { const a = D[sp - 3]; D[sp - 3] = D[sp - 2]; D[sp - 2] = D[sp - 1]; D[sp - 1] = a; break; } // ROT
      case 0x17: D[sp - 1] = (-D[sp - 1]) | 0; break; // NEG
      case 0x1b: D[sp - 1] = ~D[sp - 1]; break; // NOT
      case 0x10: case 0x11: case 0x12: case 0x13: case 0x14: case 0x15: case 0x16:
      case 0x18: case 0x19: case 0x1a: case 0x1c: case 0x1d: case 0x1e:
      case 0x20: case 0x21: case 0x22: {
        const b = D[sp - 1];
        const a = D[sp - 2];
        let r;
        if (op === 0x10) r = (a + b) | 0; // ADD
        else if (op === 0x11) r = (a - b) | 0; // SUB
        else if (op === 0x12) r = Math.imul(a, b); // MUL, low 32 bits of the exact product
        else if (op === 0x13) { if (b === 0) return done(4); r = a === -2147483648 && b === -1 ? a : (a / b) | 0; } // DIV
        else if (op === 0x14) { if (b === 0) return done(4); r = b === -1 ? 0 : (a % b) | 0; } // MOD
        else if (op === 0x15) { if (b === 0) return done(4); r = Math.floor((a >>> 0) / (b >>> 0)) | 0; } // DIVU
        else if (op === 0x16) { if (b === 0) return done(4); r = ((a >>> 0) % (b >>> 0)) | 0; } // MODU
        else if (op === 0x18) r = a & b; // AND
        else if (op === 0x19) r = a | b; // OR
        else if (op === 0x1a) r = a ^ b; // XOR
        else if (op === 0x1c) r = a << (b & 31); // SHL
        else if (op === 0x1d) r = a >> (b & 31); // SHR, arithmetic
        else if (op === 0x1e) r = (a >>> (b & 31)) | 0; // SHRU, logical
        else if (op === 0x20) r = a === b ? 1 : 0; // EQ
        else if (op === 0x21) r = a < b ? 1 : 0; // LT
        else r = (a >>> 0) < (b >>> 0) ? 1 : 0; // LTU
        sp--;
        D[sp - 1] = r;
        break;
      }
      case 0x30: case 0x31: case 0x32: { // JMP / JZ / JNZ
        const rel = ((P[next - 2] | (P[next - 1] << 8)) << 16) >> 16;
        let take = true;
        if (op !== 0x30) { const v = D[--sp]; take = op === 0x31 ? v === 0 : v !== 0; }
        if (take) pc = next + rel;
        break;
      }
      case 0x33: // CALL
        if (csp === 64) return done(7);
        C[csp++] = next;
        pc = P[next - 2] | (P[next - 1] << 8);
        break;
      case 0x34: // RET
        if (csp === 0) return done(8);
        pc = C[--csp];
        break;
      case 0x40: { // LOAD
        const ad = D[sp - 1];
        if (ad < 0 || ad > 255) return done(6);
        D[sp - 1] = M[ad];
        break;
      }
      case 0x41: { // STORE: ( v addr -- ), addr on top
        const ad = D[sp - 1];
        if (ad < 0 || ad > 255) return done(6);
        M[ad] = D[sp - 2];
        sp -= 2;
        break;
      }
      case 0x50: { // PRINT: the value in decimal ASCII
        let v = D[sp - 1];
        const neg = v < 0;
        let mag = neg ? -v : v;
        const tmp = new Uint8Array(11);
        let k = 11;
        do { tmp[--k] = 48 + (mag % 10); mag = Math.floor(mag / 10); } while (mag > 0);
        if (neg) tmp[--k] = 45;
        const len = 11 - k;
        if (olen + len > OUT_MAX) return done(11); // output limit: writes nothing
        sp--;
        out.set(tmp.subarray(k), olen);
        olen += len;
        break;
      }
      case 0x51: // PUTC
        if (olen + 1 > OUT_MAX) return done(11);
        out[olen++] = D[--sp] & 255;
        break;
      case 0x52: D[sp++] = ip < I.length ? I[ip++] : -1; break; // IN
      case 0x53: return done(D[--sp] & 255); // EXIT
    }
  }
}

const I = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const O = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
for (const id of readdirSync(I).sort()) {
  const [bytes, code] = run(
    new Uint8Array(readFileSync(join(I, id, 'program.bin'))),
    new Uint8Array(readFileSync(join(I, id, 'input.bin'))),
  );
  mkdirSync(join(O, id), { recursive: true });
  writeFileSync(join(O, id, 'stdout.bin'), bytes);
  writeFileSync(join(O, id, 'exit.txt'), `${code}\n`);
}
