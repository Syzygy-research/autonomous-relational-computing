// D2: the v2 full evaluator must fingerprint proposals with SHA-256,
// not the 32-bit FNV-1a it shipped with in the 2026-09-28 release.
//
// The sha256Hex implementation is extracted from each served corpus.html
// copy and checked against the standard FIPS 180-4 vectors and against
// node:crypto on varied inputs, so the swap is verified, not assumed.
import assert from "node:assert/strict";
import { readFileSync } from "node:fs";
import { createHash } from "node:crypto";

const copies = [
  "public/evaluator-v2-full/corpus.html",
  "docs/valis-kore-official-evaluator-v2-full/corpus.html"
];

function extractSha256Hex(html, path) {
  const start = html.indexOf("function sha256Hex(s){");
  assert.notEqual(start, -1, `${path}: sha256Hex not found`);
  const end = html.indexOf("function proposalDigest", start);
  assert.notEqual(end, -1, `${path}: proposalDigest not found after sha256Hex`);
  const src = html.slice(start, end);
  return new Function(`${src}; return sha256Hex;`)();
}

for (const path of copies) {
  const html = readFileSync(new URL(`../${path}`, import.meta.url), "utf8");
  assert.equal(html.includes("2166136261"), false, `${path}: FNV-1a fingerprint still present`);
  assert.equal(html.includes("function simpleHash"), false, `${path}: simpleHash still present`);
  // The digest call sites are the same ones the FNV function served.
  assert.ok(html.includes("return 'p-'+sha256Hex(stable(p))"), `${path}: proposalDigest does not use sha256Hex`);
  assert.ok(html.includes("'lambda-'+sha256Hex(proposalDigest(p)+after.version)"), `${path}: release id does not use sha256Hex`);

  const sha256Hex = extractSha256Hex(html, path);
  // FIPS 180-4 standard vectors.
  assert.equal(sha256Hex(""), "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855");
  assert.equal(sha256Hex("abc"), "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad");
  assert.equal(sha256Hex("abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq"), "248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1");
  assert.equal(sha256Hex("a".repeat(1000000)), "cdc76e5c9914fb9281a1c7e284d73e67f1809a48a497200e046d39ccc7112cd0");
  // Cross-check against node:crypto, including multi-byte UTF-8 input.
  for (const input of ["hello world", "{\"amount\":2500}", "✓ λ — ünïcode", "x".repeat(12345)]) {
    assert.equal(sha256Hex(input), createHash("sha256").update(input, "utf8").digest("hex"), `${path}: mismatch with node:crypto`);
  }
}

console.log("v2 corpus sha256 tests passed");
