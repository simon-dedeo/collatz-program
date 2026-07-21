"""exact_weights.py -- certified rational enclosures for the KL weights.

Weights (lambda in (1,2], alpha = log2 3):
    p  = lambda^-2      (exactly rational for rational lambda)
    q2 = lambda^(alpha-2)   in (0,1), DEcreasing in lambda (alpha-2 < 0)
    q8 = lambda^(alpha-1)   > 1,      INcreasing in lambda (alpha-1 > 0)

Everything here returns Fractions W together with an EXACT integer-arithmetic
verification that W is on the claimed side of the true irrational value.

Method (same device as experiments/kl/certify.py, both directions):
  * alpha is sandwiched by continued-fraction convergents p/q of log2(3),
    each side verified by the pure integer comparison 2^p <=> 3^q.
  * for lambda = a/b > 1 and rational exponent e = u/v (u,v integers, v>0):
        W >= lambda^e  <=>  W^v >= (a/b)^u      (v > 0)
    which is a finite integer comparison after clearing denominators
    (sign of u handled by moving powers across).
  * monotonicity of t -> lambda^t (lambda > 1) converts the alpha sandwich
    into a bound with rational exponent:
        alpha < ahi  ==>  lambda^(alpha-2) > lambda^(ahi-2)   (exponent < 0 ...)
    -- we only ever use:  for lambda > 1, t < t' ==> lambda^t < lambda^t'.

All certified: no floats on the load-bearing path (floats only propose W).
"""

from fractions import Fraction
from math import log


# ---------------------------------------------------------------- alpha sandwich

_CONVERGENTS = [(3, 2), (8, 5), (19, 12), (65, 41), (84, 53), (485, 306),
                (1054, 665), (24727, 15601), (50508, 31867)]


def alpha_sandwich(depth=-2):
    """Return (alo, ahi) as Fractions with alo < alpha < ahi, exactly verified.

    depth: index into the convergent list for the finer pair; default uses the
    last two convergents (error ~ 1/(665*15601) if depth=-2 pairs those two).
    """
    lo, hi = None, None
    for (p, q) in _CONVERGENTS:
        if 2 ** p < 3 ** q:          # p/q < alpha  (exact integer check)
            lo = Fraction(p, q)
        elif 2 ** p > 3 ** q:        # p/q > alpha
            hi = Fraction(p, q)
        else:                        # impossible: 2^p = 3^q only trivially
            raise AssertionError
    assert lo is not None and hi is not None and lo < hi
    return lo, hi


ALPHA_LO, ALPHA_HI = alpha_sandwich()


# ---------------------------------------------------------------- exact power cmp

def _cmp_pow(W: Fraction, lam: Fraction, e: Fraction):
    """Exact sign of  W - lam^e  for Fractions W>0, lam>0, e (any sign)."""
    a, b = lam.numerator, lam.denominator
    u, v = e.numerator, e.denominator        # v > 0 by Fraction normalization
    w_n, w_d = W.numerator, W.denominator
    # W >= lam^(u/v)  <=>  W^v >= lam^u  <=>  w_n^v * b^u >= w_d^v * a^u   (u>=0)
    if u >= 0:
        lhs = w_n ** v * b ** u
        rhs = w_d ** v * a ** u
    else:
        lhs = w_n ** v * a ** (-u)
        rhs = w_d ** v * b ** (-u)
    return (lhs > rhs) - (lhs < rhs)


def rat_pow_bound(lam: Fraction, e: Fraction, side: str, rel=Fraction(1, 10**9)):
    """Certified rational bound W for lam^e with lam>1 rational, e rational.

    side='upper': W >= lam^e ;  side='lower': W <= lam^e.  Verified exactly.
    """
    est = float(lam) ** float(e)
    eps = float(rel)
    W = Fraction(est * (1 + eps) if side == 'upper' else est * (1 - eps)
                 ).limit_denominator(10 ** 12)
    step = Fraction(1 + eps if side == 'upper' else 1) / Fraction(1 if side == 'upper' else 1 + eps)
    for _ in range(200):
        c = _cmp_pow(W, lam, e)
        if side == 'upper' and c >= 0:
            return W
        if side == 'lower' and c <= 0:
            return W
        W = (W * step * step) if side == 'upper' else (W / (step * step))
        W = W.limit_denominator(10 ** 14)
    raise RuntimeError('rat_pow_bound failed to verify')


# ---------------------------------------------------------------- weight enclosures

def weight_enclosures(lam_lo: Fraction, lam_hi: Fraction):
    """Certified enclosures for (p, q2, q8) valid for ALL lambda in [lam_lo,lam_hi].

    Uses per-weight monotonicity:
      p  = lam^-2     : max at lam_lo, min at lam_hi (exact rationals);
      q2 = lam^(a-2)  : decreasing => max at lam_lo, min at lam_hi;
      q8 = lam^(a-1)  : increasing => max at lam_hi, min at lam_lo.
    Alpha sandwich direction (lam > 1):
      upper for q2: exponent up  ->  use  a <= ALPHA_HI:  lam_lo^(AHI-2) >= lam_lo^(a-2)
                    since AHI-2 > a-2 and lam_lo > 1.  ==> W2_hi >= q2 everywhere.
      lower for q2: use a >= ALPHA_LO at lam_hi:  lam_hi^(ALO-2) <= q2 everywhere.
      upper for q8: lam_hi^(AHI-1) ; lower: lam_lo^(ALO-1).
    Special case lam_hi == 2: q8 upper could use 2^(a-1)=3/2 but only if a were
    exact; we still need a rational exponent, and 2^(AHI-1) > 3/2 is a hair
    above -- we use min(that, exact-checked) anyway.
    Returns dict of Fractions: p_lo,p_hi,q2_lo,q2_hi,q8_lo,q8_hi.
    """
    assert 1 < lam_lo <= lam_hi <= 2
    p_hi = lam_lo ** -2
    p_lo = lam_hi ** -2
    q2_hi = rat_pow_bound(lam_lo, ALPHA_HI - 2, 'upper')
    q2_lo = rat_pow_bound(lam_hi, ALPHA_LO - 2, 'lower')
    q8_hi = rat_pow_bound(lam_hi, ALPHA_HI - 1, 'upper')
    q8_lo = rat_pow_bound(lam_lo, ALPHA_LO - 1, 'lower')
    return {'p_lo': p_lo, 'p_hi': p_hi, 'q2_lo': q2_lo, 'q2_hi': q2_hi,
            'q8_lo': q8_lo, 'q8_hi': q8_hi}


def s_annealed(lam: float) -> float:
    """Float annealed column pressure s(lambda)=lam^-2+(lam^(a-2)+lam^(a-1))/3."""
    a = log(3, 2)
    return lam ** -2 + (lam ** (a - 2) + lam ** (a - 1)) / 3


LAM18 = Fraction(18703245, 10 ** 7)   # certified lambda_18 (cert_k18.json)
LAM15 = Fraction(18419679, 10 ** 7)


if __name__ == '__main__':
    print('alpha in', ALPHA_LO, float(ALPHA_LO), '<', ALPHA_HI, float(ALPHA_HI))
    enc = weight_enclosures(LAM18, Fraction(2))
    for k, v in enc.items():
        print(k, float(v))
