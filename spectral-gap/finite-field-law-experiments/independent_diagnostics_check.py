#!/usr/bin/env python3
"""Read-only statistical recomputation; no graph generation or rank calls."""
from pathlib import Path
import csv,json,math,statistics
ROOT=Path(__file__).resolve().parent

def close(a,b):
    assert math.isclose(a,b,rel_tol=1e-12,abs_tol=1e-12),(a,b)

def main():
    data={}
    for path in [ROOT/'samples.csv',ROOT/'followup'/'samples.csv']:
        for row in csv.DictReader(path.open()):
            key=(int(row['N']),int(row['sample']))
            assert key not in data
            data[key]={'x0':int(row['excess_lambda0']),'x2':int(row['excess_lambda2']),
                       'twins':int(row['adjacent_twin_pairs']) if 'adjacent_twin_pairs' in row else None}
    main_diag=list(csv.DictReader((ROOT/'main-twin-diagnostics.csv').open()))
    seen=set()
    for row in main_diag:
        key=(int(row['N']),int(row['sample']))
        assert key not in seen;seen.add(key)
        assert data[key]['x2']==int(row['excess_lambda2'])
        data[key]['twins']=int(row['adjacent_twin_pairs'])
    assert len(main_diag)==7200 and len(data)==8600
    diag=json.loads((ROOT/'diagnostics.json').read_text())
    checked=[]
    conditional_bins={}
    for row in csv.DictReader((ROOT/'conditional-no-twins-histograms.csv').open()):
        key=(int(row['N']),int(row['excess']))
        assert key not in conditional_bins;conditional_bins[key]=row
    z=statistics.NormalDist().inv_cdf(.975)
    for group in diag['groups']:
        N,m=group['N'],group['samples']
        records=[r for (g,i),r in data.items() if g==N]
        assert len(records)==m and all(r['twins'] is not None for r in records)
        assert all(r['twins']==0 or r['x2']>0 for r in records)
        pairs=[r['twins'] for r in records]
        assert group['twin_graphs']==sum(x>0 for x in pairs)
        close(group['twin_fraction'],sum(x>0 for x in pairs)/m)
        close(group['mean_twin_pairs'],statistics.mean(pairs))
        close(group['mean_twin_pairs_SE'],statistics.stdev(pairs)/math.sqrt(m))
        close(group['exact_expected_twin_pairs'],6/N)
        for label,key in [('lambda0','x0'),('lambda2','x2')]:
            vals=[r[key] for r in records]
            inf=group['moment_influence_'+label]
            weights=sorted([3**x for x in vals],reverse=True)
            total=sum(weights);top=max(1,math.ceil(.01*m))
            assert inf['samples']==m and inf['maximum_excess']==max(vals)
            assert inf['maximum_single_weight']==weights[0] and inf['top_one_percent_count']==top
            close(inf['mean'],total/m)
            close(inf['sample_SE'],statistics.stdev(weights)/math.sqrt(m))
            close(inf['maximum_single_contribution_to_mean'],weights[0]/m)
            close(inf['maximum_single_fraction_of_total_weight'],weights[0]/total)
            close(inf['top_one_percent_fraction_of_total_weight'],sum(weights[:top])/total)
        vals=[r['x2'] for r in records if r['twins']==0]
        cond=group['lambda2_conditional_no_twins']
        assert cond['samples']==len(vals)
        hist={k:vals.count(k) for k in range(max(vals)+1)}
        assert {int(k):v for k,v in cond['histogram'].items()}==hist
        for b in cond['bins']:
            k,c=b['excess'],hist.get(b['excess'],0);p=c/len(vals)
            assert b['count']==c
            close(b['frequency'],p)
            close(b['binomial_SE'],math.sqrt(p*(1-p)/len(vals)))
            den=1+z*z/len(vals);center=(p+z*z/(2*len(vals)))/den
            half=z*math.sqrt(p*(1-p)/len(vals)+z*z/(4*len(vals)**2))/den
            close(b['wilson95_low'],max(0,center-half));close(b['wilson95_high'],min(1,center+half))
            row=conditional_bins[(N,k)]
            assert int(row['count'])==c and int(row['conditional_samples'])==len(vals)
            close(float(row['frequency']),p);close(float(row['binomial_SE']),b['binomial_SE'])
            close(float(row['wilson95_low']),b['wilson95_low']);close(float(row['wilson95_high']),b['wilson95_high'])
        checked.append({'N':N,'samples':m,'no_twin_samples':len(vals),
                        'conditional_histogram_verified':True,'both_moment_influence_tables_verified':True,
                        'twin_summaries_verified':True})
    assert diag['total_graph_samples']==len(data)==8600
    assert diag['total_modular_rank_computations']==2*len(data)==17200
    result={'status':'PASS','graph_generation_calls':0,'modular_rank_calls':0,
            'raw_rows_joined':len(data),'main_twin_rows_joined':len(main_diag),
            'verified_groups':checked,'followup_seed_header_resolved':
            'Fixed study seed: 2026111501409' in (ROOT/'followup'/'REPORT.txt').read_text(),
            'followup_marked_exploratory':(ROOT/'followup'/'REPORT.txt').read_text().startswith('EXPLORATORY FOLLOW-UP')}
    assert result['followup_seed_header_resolved'] and result['followup_marked_exploratory']
    (ROOT/'independent-diagnostics-checks.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))

if __name__=='__main__':main()
