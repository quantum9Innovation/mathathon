#!/usr/bin/env python3
"""Independent checks only: no full experiment or old regression is run."""
from pathlib import Path
import csv
from decimal import Decimal, getcontext
import hashlib
import importlib.util
import json
import math
import random
import statistics
import sys
sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location('new_k4_corank_experiment', ROOT/'k4_corank_experiment.py')
exp = importlib.util.module_from_spec(spec)
spec.loader.exec_module(exp)
np = exp.np


def reference_rank(M, p):
    """Independent all-row/full-row pure Python RREF, unlike NumPy forward tails."""
    A = [[int(x) % p for x in row] for row in M]
    m, n = len(A), len(A[0])
    r = 0
    for j in range(n):
        at = next((i for i in range(r, m) if A[i][j]), None)
        if at is None:
            continue
        A[r], A[at] = A[at], A[r]
        inv = pow(A[r][j], -1, p)
        A[r] = [x*inv % p for x in A[r]]
        for i in range(m):
            if i != r and A[i][j]:
                factor = A[i][j]
                A[i] = [(a-factor*b) % p for a,b in zip(A[i], A[r])]
        r += 1
        if r == m:
            break
    return r


def close(a, b, *, rel=1e-12, abs_tol=1e-13):
    assert math.isclose(a,b,rel_tol=rel,abs_tol=abs_tol), (a,b)


def main():
    protected = [ROOT/x for x in ['k4_corank_experiment.py','results.json','samples.csv','histograms.csv','REPORT.txt']]
    before = {p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in protected}
    results = json.loads((ROOT/'results.json').read_text())
    raw = list(csv.DictReader((ROOT/'samples.csv').open(newline='')))
    groups = {}
    for row in raw:
        N, i = int(row['N']), int(row['sample'])
        groups.setdefault(N, {})
        assert i not in groups[N]
        values = tuple(int(row[k]) for k in ['nullity_lambda0','excess_lambda0','nullity_lambda2','excess_lambda2'])
        assert values[0] == values[1]+1 and values[2] == values[3]+3
        assert min(values) >= 0
        groups[N][i] = values
    assert len(raw) == sum(results['actual_fixed_targets']) == 7200
    # Exact first-two prefix replay only, with the SAME NumPy version/streams.
    streams = np.random.SeedSequence(exp.SEED).spawn(len(exp.SIZES))
    prefix = []
    for N, stream in zip(exp.SIZES, streams):
        rng = np.random.default_rng(stream)
        for sample in range(1,3):
            A = exp.sample_k4_lift(N,rng)
            assert np.array_equal(A,A.T) and np.all(A.sum(axis=1)==3) and np.all(np.diag(A)==0)
            ranks=[]
            for lam,old in [(0,1),(2,3)]:
                shifted=A.copy()
                for i in range(len(A)):
                    shifted[i,i] -= lam
                py=reference_rank(shifted.tolist(),3)
                num=exp.rank_mod_numpy(shifted,3)
                assert py==num
                nullity=len(A)-py
                ranks.append((nullity,nullity-old))
            csv_values=groups[N][sample]
            assert (ranks[0][0],ranks[0][1],ranks[1][0],ranks[1][1])==csv_values
            prefix.append({'N':N,'sample':sample,'shape':list(A.shape),
                           'adjacency_sha256':hashlib.sha256(A.tobytes()).hexdigest(),
                           'nullity_lambda0':ranks[0][0],'excess_lambda0':ranks[0][1],
                           'nullity_lambda2':ranks[1][0],'excess_lambda2':ranks[1][1],
                           'both_exact_rank_methods_agree':True,'matches_raw_csv':True})
    # NEW independent small matrices, including rectangular/swap/zero-column cases.
    rng=random.Random(51230169)
    checked=0
    for p in [3,5]:
        for m,n in [(1,1),(1,7),(7,1),(2,8),(8,2),(6,9),(9,6),(12,12)]:
            for rep in range(6):
                M=[[rng.randrange(-6,7) for _ in range(n)] for _ in range(m)]
                assert reference_rank(M,p)==exp.rank_mod_numpy(M,p)
                checked+=1
    for M in [[[0,0,1],[0,1,0],[1,0,0]],[[0]*9 for _ in range(7)],
              [[0,1,0,2],[0,1,0,2],[0,0,0,0]], [[0,0,1,2],[0,0,2,1]]]:
        assert reference_rank(M,3)==exp.rank_mod_numpy(M,3)
        checked+=1
    # Independently recompute all histogram/statistical outputs from raw CSV.
    getcontext().prec=80
    weights=[Decimal(1)]
    for k in range(1,60):
        weights.append(weights[-1]/Decimal(3**k-1))
    C=1/sum(weights)
    reference=[float(C*w) for w in weights]
    close(float(C),results['reference']['normalizing_constant'])
    close(sum((3**k)*reference[k] for k in range(len(reference))),2)
    z=statistics.NormalDist().inv_cdf(.975)
    summaries=[]
    for group in results['groups']:
        N,m=group['N'],group['samples']
        assert set(groups[N])==set(range(1,m+1))
        for label,at in [('0',1),('2',3)]:
            vals=[groups[N][i][at] for i in range(1,m+1)]
            hist={k:vals.count(k) for k in set(vals)}
            info=group['shifts'][label]
            assert {int(k):v for k,v in info['histogram'].items()}=={k:hist.get(k,0) for k in range(max(hist)+1)}
            for b in info['bins']:
                k,c=b['excess'],hist.get(b['excess'],0)
                assert b['count']==c
                f=c/m
                close(b['frequency'],f)
                close(b['binomial_SE'],math.sqrt(f*(1-f)/m))
                den=1+z*z/m
                center=(f+z*z/(2*m))/den
                half=z*math.sqrt(f*(1-f)/m+z*z/(4*m*m))/den
                close(b['wilson95_low'],max(0,center-half))
                close(b['wilson95_high'],min(1,center+half))
                close(b['reference_probability'],reference[k])
                close(b['reference_expected_count'],m*reference[k])
                nullse=math.sqrt(reference[k]*(1-reference[k])/m)
                close(b['reference_binomial_SE'],nullse)
                close(b['reference_standardized_difference'],(f-reference[k])/nullse)
            tv=sum(abs(hist.get(k,0)/m-reference[k]) for k in range(len(reference)))/2
            close(info['empirical_total_variation_from_reference'],tv)
            powers=[3**k for k in vals]
            close(info['mean_p_to_excess'],statistics.mean(powers))
            close(info['mean_p_to_excess_SE'],statistics.stdev(powers)/math.sqrt(m))
            summaries.append({'N':N,'lambda':int(label),'histogram':hist,
                              'raw_statistics_verified':True,'TV':tv,
                              'pooled_at_least_four_count':sum(v for k,v in hist.items() if k>=4)})
    for contrast in results['divisibility_contrasts']:
        Na,Nb,lam=contrast['divisible_N'],contrast['neighbor_N'],contrast['lambda']
        at=1 if lam==0 else 3
        a=sum(v[at]==0 for v in groups[Na].values())/len(groups[Na])
        b=sum(v[at]==0 for v in groups[Nb].values())/len(groups[Nb])
        se=math.sqrt(a*(1-a)/len(groups[Na])+b*(1-b)/len(groups[Nb]))
        close(contrast['difference'],a-b);close(contrast['SE'],se);close(contrast['z'],(a-b)/se)
    after={p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in protected}
    assert before==after
    output={'status':'PASS','numpy_version':np.__version__,'python_version':sys.version,
            'prefix_graphs_replayed_only':8,'prefix_shifted_rank_comparisons':16,
            'prefix_records':prefix,'new_independent_matrix_checks':checked,
            'raw_main_records_verified':len(raw),'histogram_statistical_summaries_verified':summaries,
            'reference_C_high_precision':str(C),'reference_mean_three_to_excess':2,
            'primary_files_unchanged':True,'protected_hashes':before,
            'full_sampler_rerun':False,'old_code_or_tests_imported':False}
    (ROOT/'independent-rank-and-statistics-checks.json').write_text(json.dumps(output,indent=2)+'\n')
    print(json.dumps({'status':'PASS','numpy_version':np.__version__,
                      'prefix_graphs_replayed_only':8,'exact_rank_comparisons':16,
                      'new_matrix_checks':checked,'raw_records_verified':len(raw),
                      'primary_files_unchanged':True},indent=2))


if __name__=='__main__':
    main()
