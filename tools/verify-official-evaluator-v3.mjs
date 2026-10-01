import { readFileSync, existsSync } from 'node:fs';
import { createHash } from 'node:crypto';

const expectedZipHash = '767a13d6f927950adc43636ac7831e309ad51f570f7410f177be359140941404';
const required = [
  'docs/corpus/sources/official-evaluator-v3-programmable-consequence/VALIS-KORE_Official_Evaluator_v3_Programmable_Consequence.zip',
  'docs/valis-kore-official-evaluator-v3-programmable-consequence/index.html',
  'docs/valis-kore-official-evaluator-v3-programmable-consequence/corpus.html',
  'docs/valis-kore-official-evaluator-v3-programmable-consequence/manifest.json',
  'public/evaluator-v2-full/index.html',
  'public/evaluator-v2-full/corpus.html',
  'public/evaluator-v2-full/manifest.json',
  'public/evaluator-v3-programmable-consequence/index.html',
  'public/evaluator-v3-programmable-consequence/manifest.json'
];

function sha256(path) {
  return createHash('sha256').update(readFileSync(path)).digest('hex');
}

let failed = false;
for (const path of required) {
  if (!existsSync(path)) {
    console.error(`missing: ${path}`);
    failed = true;
  }
}

if (!failed) {
  const zipHash = sha256(required[0]);
  if (zipHash !== expectedZipHash) {
    console.error(`zip hash mismatch: ${zipHash}`);
    failed = true;
  }

  const manifests = [
    ['docs', JSON.parse(readFileSync('docs/valis-kore-official-evaluator-v3-programmable-consequence/manifest.json', 'utf8'))],
    ['public', JSON.parse(readFileSync('public/evaluator-v2-full/manifest.json', 'utf8'))]
  ];

  for (const [name, data] of manifests) {
    if (data.artifact !== 'VALIS-KORE Official Evaluator') {
      console.error(`${name} manifest artifact mismatch`);
      failed = true;
    }
    if (data.version !== '3.0-programmable-consequence') {
      console.error(`${name} manifest version mismatch`);
      failed = true;
    }
    if (data.package_sha256 !== expectedZipHash) {
      console.error(`${name} manifest package hash mismatch`);
      failed = true;
    }
    if (data.evidence_boundary?.production_conformance !== 'OPEN') {
      console.error(`${name} manifest production boundary mismatch`);
      failed = true;
    }
    if (data.evidence_boundary?.decision_volume_interaction !== 'ILLUSTRATIVE_NOT_EVIDENCE') {
      console.error(`${name} manifest illustrative boundary mismatch`);
      failed = true;
    }
    if (data.included_full_corpus !== 'corpus.html') {
      console.error(`${name} manifest full corpus mismatch`);
      failed = true;
    }
  }

  const index = readFileSync('public/evaluator-v2-full/index.html', 'utf8');
  const corpus = readFileSync('public/evaluator-v2-full/corpus.html', 'utf8');
  const requiredText = [
    'A decision is not a consequence.',
    'Programmable Consequence',
    'Consequential Reachability',
    'Illustrative visualization only',
    'not an empirical VALIS result'
  ];
  for (const text of requiredText) {
    if (!index.includes(text)) {
      console.error(`public index missing: ${text}`);
      failed = true;
    }
  }
  if (index.includes('100,000')) {
    console.error('public index contains removed synthetic 100,000 decision wording');
    failed = true;
  }
  if (!corpus.includes('VALIS-KORE') || corpus.length < 100000) {
    console.error('public corpus missing expected full corpus content');
    failed = true;
  }
}

if (failed) process.exit(1);
console.log('official evaluator v3 programmable consequence verified');
