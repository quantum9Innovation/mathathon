from fractions import Fraction
from itertools import permutations
from math import comb, factorial, prod

n = 8
total = 0
for sigma in permutations(range(n)):
    value = 1
    for row in range(4):
        for column in (2 * row, 2 * row + 1):
            value *= n * int(sigma[row] == column) - 1
    total += value
actual = Fraction(total, factorial(n))
formula = sum(
    Fraction(comb(4, count) * (-2) ** count * n**count, prod(range(n - count + 1, n + 1)))
    for count in range(5)
)
assert total == 430464
assert actual == formula == Fraction(1121, 105)
assert actual - (n - 1) == Fraction(386, 105)
print('Exact direct enumeration and compatible-subset expansion agree')
print('Permutations:', factorial(n))
print('Integer sum:', total)
print('Scaled moment:', actual)
print('Scaled clique value:', n - 1)
print('Excess:', actual - (n - 1))
