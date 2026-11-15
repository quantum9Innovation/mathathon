"""Outward-rounded finite certificate for the n=12 balanced Ganelius rule.

No third-party packages. Decimal exp, ln, and sqrt are correctly rounded;
we expand each result by one adjacent representable number. All algebraic
operations use directed rounding. Pi is bounded by exact rational Machin
series with alternating-series remainders, not a decimal literal.
"""

from decimal import Context, Decimal, ROUND_FLOOR, ROUND_CEILING, ROUND_HALF_EVEN
from fractions import Fraction
from hashlib import sha256
import time


PRECISION = 64
DOWN = Context(prec=PRECISION, rounding=ROUND_FLOOR)
UP = Context(prec=PRECISION, rounding=ROUND_CEILING)
NEAR = Context(prec=PRECISION, rounding=ROUND_HALF_EVEN)
D = Decimal
ZERO = D(0)
ONE = D(1)


def exact(x):
    x = D(x)
    return x, x


def rational(x):
    return DOWN.divide(D(x.numerator), D(x.denominator)), UP.divide(D(x.numerator), D(x.denominator))


def add(x, y):
    return DOWN.add(x[0], y[0]), UP.add(x[1], y[1])


def sub(x, y):
    return DOWN.subtract(x[0], y[1]), UP.subtract(x[1], y[0])


def mul(x, y):
    return min(DOWN.multiply(a, b) for a in x for b in y), max(UP.multiply(a, b) for a in x for b in y)


def sqrt(x):
    assert x[0] >= 0
    lo, hi = NEAR.sqrt(x[0]), NEAR.sqrt(x[1])
    return max(ZERO, NEAR.next_minus(lo)), NEAR.next_plus(hi)


def ln(x):
    assert x[0] > 0
    return NEAR.next_minus(NEAR.ln(x[0])), NEAR.next_plus(NEAR.ln(x[1]))


def atan_fraction_bounds(q, terms):
    x = Fraction(1, q)
    total = sum(((-1) ** k * x ** (2*k+1) / (2*k+1) for k in range(terms)), Fraction(0))
    next_total = total + (-1) ** terms * x ** (2*terms+1) / (2*terms+1)
    return min(total, next_total), max(total, next_total)


def pi_bounds():
    # Machin: pi=16 atan(1/5)-4 atan(1/239). Alternating remainders.
    a = atan_fraction_bounds(5, 100)
    b = atan_fraction_bounds(239, 40)
    lo = 16*a[0] - 4*b[1]
    hi = 16*a[1] - 4*b[0]
    return rational(lo)[0], rational(hi)[1]


def ganelius_log_nodes(n, pi):
    # r=1/4: ceil((pi/4)sqrt(nr))=ceil(pi sqrt(n)/8).
    tail = mul(mul(pi, sqrt(exact(n))), exact(D('0.125')))
    c_lo = tail[0].to_integral_value(rounding=ROUND_CEILING)
    c_hi = tail[1].to_integral_value(rounding=ROUND_CEILING)
    assert c_lo == c_hi
    n0 = n-int(c_lo)
    assert n0>3 and n-n0-1>0
    twice_pi = mul(exact(2), pi)
    baseline = sqrt(exact(n0))
    nodes = [mul(twice_pi, sub(sqrt(exact(j-1)), baseline)) for j in range(1, n0+1)]
    nodes += [mul(twice_pi, sub(sqrt(exact(D(n0)-D('0.5'))), baseline))]
    for j in range(n0+2,n+1):
        node = Fraction(1) - Fraction(j-n0-1,5*(n-n0-1))
        nodes.append(ln(rational(node)))
    assert len(nodes)==n
    return nodes, n0


def exp_upper(x):
    return NEAR.next_plus(NEAR.exp(x))


def tanh_half_upper(distance):
    # distance >= 0, monotonicity in distance. If w is a LOWER bound
    # on exp(-distance), then (1-w)/(1+w) is an UPPER bound.
    assert distance >= 0
    w = max(ZERO, NEAR.next_minus(NEAR.exp(distance.copy_negate())))
    numerator = UP.subtract(ONE,w)
    denominator = DOWN.add(ONE,w)
    return UP.divide(numerator,denominator)


def cell_d_upper(lo, hi, lognodes):
    result = exp_upper(UP.divide(hi,D(2)))
    for a in lognodes:
        delta = sub((lo,hi),a)
        distance = max(delta[0].copy_abs(),delta[1].copy_abs())
        factor = tanh_half_upper(distance)
        result = UP.multiply(result,UP.multiply(factor,factor))
    return result


def run(n=12,target_e='0.0000005',tail_u=-30):
    started=time.monotonic()
    pi=pi_bounds()
    lognodes,n0=ganelius_log_nodes(n,pi)
    constant=add(mul(exact(2),pi),exact(4))[1]
    target=D(target_e)
    # For u<=tail_u, |B(exp u)|<=1 gives d^2<=exp(u).
    tail_e=UP.multiply(constant,exp_upper(D(tail_u)))
    assert tail_e<=target
    pending=[(D(tail_u),ZERO,0)]
    visited=0; accepted=0; maxdepth=0; largest_accepted=ZERO
    partition=sha256()
    while pending:
        lo,hi,depth=pending.pop()
        visited+=1
        d=cell_d_upper(lo,hi,lognodes)
        bound=UP.multiply(constant,UP.multiply(d,d))
        if bound<=target:
            accepted+=1
            largest_accepted=max(largest_accepted,bound)
            partition.update(f'{lo}\t{hi}\t{bound}\n'.encode())
            continue
        assert depth<64 and visited<1000000, 'Certificate failed to close.'
        mid=NEAR.divide(NEAR.add(lo,hi),D(2))
        assert lo<mid<hi
        maxdepth=max(maxdepth,depth+1)
        pending.append((mid,hi,depth+1))
        pending.append((lo,mid,depth+1))
    print('precision:',PRECISION)
    print('pi interval:',*pi)
    print('Ganelius n:',n,'n0:',n0,'rational m:',2*n+1)
    print('lower/upper PSD block counts:',4*n+2,4*n+3,'each of order 2N')
    print('target e:',target)
    print('tail e bound:',tail_e)
    print('largest accepted cell e bound:',largest_accepted)
    print('visited cells:',visited,'accepted cells:',accepted,'max depth:',maxdepth)
    print('partition SHA256:',partition.hexdigest())
    print('CERTIFIED: e_m <=',target)
    print('CERTIFIED: eta_m=2 e_m/(1+e_m) < 0.000001')
    print('seconds:',round(time.monotonic()-started,3))


if __name__=='__main__':
    run()
