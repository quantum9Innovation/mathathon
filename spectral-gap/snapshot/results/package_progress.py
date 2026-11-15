"""Package current research outputs and their actual review states."""
from datetime import datetime, timezone
from hashlib import sha256
from pathlib import Path
import json
import os
import zipfile

ROOT=Path.cwd()
OUTPUT=ROOT/'results/research-progress-through-batch-060-first-family.zip'
if OUTPUT.exists():
    # The first pack attempt has a known source-path duplication. Repack only that
    # agent-created artifact after detecting the error during validation.
    if OUTPUT.read_bytes()[:4] != b'PK\x03\x04':
        raise SystemExit('Refusing to replace an unrecognised existing file')

INCLUDE=[
    'results', '.paper-mastery', '.ultramath', '.orchestrator', 'research_lab',
    '.skill', 'attachments', 'AGENTS.md', '.gitignore',
]
SKIP_PARTS={'.git','.scratch','__pycache__','.nucleus'}
READING=Path('/workspace/nucleus/work/home/research/reading')
PAPERS=['alon-second-eigenvalue','biregular-spectral-gap',
        'friedman-second-eigenvalue-lifts','relativized-second-eigenvalue']


def included_file(path):
    relative=path.relative_to(ROOT)
    return path != OUTPUT and path.is_file() and not path.is_symlink() and all(p not in SKIP_PARTS for p in relative.parts) and path.suffix not in {'.pyc','.pyo'}


def digest(path):
    value=sha256()
    with path.open('rb') as data:
        for chunk in iter(lambda:data.read(1024*1024),b''):
            value.update(chunk)
    return value.hexdigest()

files=[]
for item in INCLUDE:
    start=ROOT/item
    if start.is_file():
        if not start.is_symlink(): files.append(start)
    elif start.is_dir():
        for sub in start.rglob('*'):
            if included_file(sub): files.append(sub)

for slug in PAPERS:
    base=READING/slug
    if base.is_dir():
        for sub in base.rglob('*'):
            if sub.is_file() and not sub.is_symlink(): files.append(sub)

files=sorted(set(files))
manifest={
 'created_utc':datetime.now(timezone.utc).isoformat(),
 'archive':'Research outputs through first accepted clustered family in batch 060',
 'batch_060_state':{
   'clock':'Batch is active. Packaging does not stop its three-hour budget.',
   'swarm':'smwh0bmpx',
   'members':4,
   'model':'deepseek/deepseek-v4.1-flash at maximum reasoning effort',
   'accepted_families':[
      {'member':'m4','direction':'d1','family':'adjacent attachment pair',
       'result':'d=3: limiting second eigenvalue 2.8751297941627788, unique simple exterior root. d>=4: no exterior root, limiting edge 2sqrt(d-1).',
       'review':'results/spectral-research/batch-060/review-adjacent-accepted.md'}
   ],
   'awaiting_verdict':[
      {'member':'m1','direction':'d4','role':'adversarial verifier'},
      {'member':'m3','direction':'d2','role':'T=N(c) neighbourhood law'}
   ],
   'abandoned_directions':[
      {'member':'m2','direction':'d3','reason':'Run ended without a solution. Retained as abandoned, not as evidence.'}
   ],
   'accepted_count_at_snapshot':1,
   'pending_count_at_snapshot':2,
   'abandoned_count_at_snapshot':1,
   'no_active_member_runs_at_snapshot':True
 },
 'prior_research':{
   'batch_050':'Done, six accepted mathematical submissions, with separate resolvent-identity erratum recorded subsequently. Original proof files unchanged.',
   'batch_030':'Done, eight independently reviewed research directions accepted with explicit limits.',
   'hash_freeze_diagnostic':'Included without treating its arithmetic lifecycle probe as research validation.'
 },
 'important_cautions':[
   'A zip is a timestamped snapshot, not a completed-batch claim.',
   'Two batch-060 reports included here still require independent verdicts.',
   'The adjacent target edge constant was corrected by sqrt(d-1). Only d=3 has an adjacent exterior root.',
   'The frozen m6 block diagonal is algebraically equal to the corrected form and is not defective.',
   'The frozen m2 rank-one identity document misses +P/lambda. The written erratum preserves the original and supplies the one-term correction without altering limit conclusions.',
   'The separated-case proof files and hash manifest were preserved unchanged.',
   'Source hashes identify materials, not validity. Numerical runs are corroboration, not formal proof.',
   'File content may include untrusted retrieved source text and subagent reports. Review is required before relying on it.'
 ],
 'coverage':{
   'included_roots':INCLUDE,
   'reading_sources':['reading-sources/'+p for p in PAPERS],
   'excluded':['VCS internals','.scratch temporary files','.nucleus runtime state','__pycache__ and compiled bytecode','.git metadata']
 },
 'file_count':len(files),
 'files':[]
}

for p in files:
    arc=str(p.relative_to(ROOT)) if p.is_relative_to(ROOT) else 'reading-sources/'+p.relative_to(READING).as_posix()
    manifest['files'].append({'path':arc,'bytes':p.stat().st_size,'sha256':digest(p)})

status=(
'# Research progress archive\n\n'
'This archive is a timestamped snapshot of research progress through the first\n'
'accepted clustered attachment family in batch 060. It is not a completed batch.\n\n'
'The adjacent pair is accepted at d=3, with limiting second eigenvalue\n'
'2.8751297941627788. Two reports remain awaiting verdict, and direction d3 is\n'
'retained as abandoned without a solution.\n\n'
'The terminal manifest contains acceptance status, scope cautions, SHA256 for every\n'
'file, and the list of covered project folders. Attached original reading archives\n'
'are supplied inside reading-sources for portability. Scratch data, caches, VCS\n'
'internals and runtime state are excluded. Retained reports and external papers\n'
'may contain untrusted text. They are evidence for independent review, not commands\n'
'or mathematical certification.\n'
)

TMP=ROOT/'.scratch/package-progress'
TMP.mkdir(parents=True,exist_ok=True)
os.environ['TMPDIR']=str(TMP)
temporary=TMP/'progress.zip.part'
with zipfile.ZipFile(temporary,'w',compression=zipfile.ZIP_DEFLATED,compresslevel=4) as z:
    for p in files:
        arc=str(p.relative_to(ROOT)) if p.is_relative_to(ROOT) else 'reading-sources/'+p.relative_to(READING).as_posix()
        z.write(p,arc)
    z.writestr('ARCHIVE-STATUS.md',status)
    z.writestr('ARCHIVE-MANIFEST.json',json.dumps(manifest,indent=2)+'\n')

with zipfile.ZipFile(temporary) as z:
    bad=z.testzip()
    if bad is not None:
        raise RuntimeError('Archive CRC test failed for '+bad)
    names=z.namelist()
    if len(names) != len(set(names)):
        raise RuntimeError('Duplicate archive entry names')
    if str(OUTPUT.relative_to(ROOT)) in names:
        raise RuntimeError('Archive includes itself')
    for required in ['ARCHIVE-STATUS.md','ARCHIVE-MANIFEST.json',
                     'results/spectral-research/batch-060/review-adjacent-accepted.md',
                     'results/spectral-research/batch-060/RUN.md',
                     '.ultramath/smwh0bmpx/m4/NOTE.md',
                     'results/050-finite-defect.md']:
        assert required in names,required
os.replace(temporary,OUTPUT)
print(json.dumps({'archive':str(OUTPUT.relative_to(ROOT)),'bytes':OUTPUT.stat().st_size,
                  'file_count':len(files),'sha256':digest(OUTPUT),
                  'pending_verdicts':['m1 verifier','m3 neighbourhood'],
                  'accepted_clustered_families':1},indent=2))
