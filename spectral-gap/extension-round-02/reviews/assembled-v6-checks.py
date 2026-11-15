from pathlib import Path
import json
import mpmath as mp

mp.mp.dps = 80
ROOT = Path('/home/acru/Documents/ChatGPT/Math4I/mathathon/spectral-gap')
FROZEN = ROOT/'manuscript-round-01/frozen-manuscript-v6'


def ratios(n, largest):
    even = odd = mp.mpf(1)
    values = {}
    for m in range(1, largest//2+1):
        even = mp.mpf(n)/(n-2*m+1)*even + mp.mpf(4*(2*m-1)*(2*m-2))/(3*(n-2*m+1))*odd
        values[2*m] = even
        if 2*m+1 <= largest:
            odd = mp.mpf(3*n)/((n-2*m)*(2*m+1))*even + mp.mpf((2*m-2)*n)/((n-2*m)*(2*m+1))*odd
            values[2*m+1] = odd
    return values


def corrected(n, k, ratio):
    big_k = k-k%2
    lam = mp.mpf(2)*mp.sqrt(mp.mpf(big_k)**3/n)/3
    hyper = mp.cosh(lam) if k%2==0 else mp.sinh(lam)/lam
    return ratio/(hyper*mp.exp(mp.mpf(k)**2/(4*n)))


data=json.loads((FROZEN/'figures/rate-and-hierarchy-data.json').read_text())
figure_checks=0
for n in sorted({row['N'] for row in data['signed_error']+data['hierarchy']}):
    rows=[row for row in data['signed_error']+data['hierarchy'] if row['N']==n]
    values=ratios(n,max(row['k'] for row in rows))
    for row in [r for r in data['signed_error'] if r['N']==n]:
        expected=mp.root(n,4)*(corrected(n,row['k'],values[row['k']])-1)
        assert abs(expected-row['scaled_error']) < mp.mpf('1e-12')
        figure_checks+=1
    for row in [r for r in data['hierarchy'] if r['N']==n]:
        expected=mp.log(corrected(n,row['k'],values[row['k']]))
        assert abs(expected-row['log_ratio_after_quartic']) < mp.mpf('1e-12')
        figure_checks+=1

correction_rows=[]
for n in [4096,65536,1048576]:
    sqrt_n=mp.sqrt(n)
    values=ratios(n,int(2*sqrt_n))
    for c in [mp.mpf('0.125'),mp.mpf('0.5'),mp.mpf(1),mp.mpf(2)]:
        residual=mp.mpf(0)
        scaled_max=mp.mpf(0)
        maximizing_order=0
        for k in range(2,int(c*sqrt_n)+1):
            w=corrected(n,k,values[k])
            scale=mp.mpf(k)/sqrt_n
            psi=(2*(k%2)-1)*mp.sqrt(scale)/2+mp.mpf(2)*scale**mp.mpf('2.5')/15
            scaled=mp.root(n,4)*(w-1)
            residual=max(residual,abs(scaled-psi))
            if abs(scaled)>scaled_max:
                scaled_max=abs(scaled)
                maximizing_order=k
        target=mp.sqrt(c)/2+mp.mpf(2)*c**mp.mpf('2.5')/15
        correction_rows.append({'N':n,'C':str(c),
            'scaled_sup_error':mp.nstr(scaled_max,22),
            'limiting_sharp_constant':mp.nstr(target,22),
            'sup_first_correction_residual':mp.nstr(residual,22),
            'maximizing_order':maximizing_order})

record={'figure_data_points_verified':figure_checks,'figure_comparison_tolerance':'1e-12',
        'decimal_precision':mp.mp.dps,'first_correction_rows':correction_rows,
        'scope':'Numerical corroboration of new figure data and the assembled first-correction formula. No interval certificate or substitute for the proof.'}
out=ROOT/'extension-round-02/reviews/assembled-v6-check-results.json'
out.write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps({'figure_points':figure_checks,'correction_ranges':len(correction_rows),'last_four':correction_rows[-4:]},indent=2))
