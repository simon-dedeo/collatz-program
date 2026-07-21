"""Decisive checks after gpt cross-check:
(A) normalization X_j = 2^{-j} B_j gives CDG walk X->X/2 or (3X+1)/2 ;
(B) per-step L^2 Fourier decay rate lambda(p): constant (=> e^{-ck}) or ~1/(log p)^2
    (=> only gpt's weak bound). Uses Bernoulli(1/2) exact distribution."""
import math
import numpy as np
from fourier_check import bernoulli_dist_series, fourier


def check_normalization():
    p = 101
    # simulate B_j and X_j=2^{-j}B_j; verify X recursion
    inv2 = pow(2, -1, p)
    B = 0
    X = 0  # X_0 = 2^0 * B_0 = 0
    bits = [1, 0, 1, 1, 0, 1, 0, 0, 1, 1]
    ok = True
    for j, e in enumerate(bits):
        Bn = (3 * B + pow(2, j, p)) % p if e else B
        # predicted X_{j+1}
        Xn_pred = ((3 * X + 1) * inv2) % p if e else (X * inv2) % p
        Bn_over = (Bn * pow(inv2, j + 1, p)) % p
        if Xn_pred != Bn_over:
            ok = False
        B, X = Bn, Bn_over
    print("(A) normalization X_j=2^-j B_j -> CDG walk X/2 | (3X+1)/2 :",
          "OK" if ok else "FAIL")


def decay_rate():
    print("\n(B) per-step L2 Fourier decay rate lambda(p) in linear regime:")
    print("    p    logp   lambda   lambda*(logp)^2   lambda/[1]")
    for p in [31, 101, 251, 601, 1201, 2003, 4057, 6553]:
        k = min(60, int(5 * math.log(p)) + 6)
        ser = bernoulli_dist_series(p, k)
        ys = []
        for j in range(4, k + 1):
            h = fourier(ser[j], p)
            m2 = float(np.sum(np.abs(h[1:]) ** 2))
            ys.append((j, math.log(m2) if m2 > 0 else -50))
        # fit slope over the middle (linear) portion, before hitting floor ~ -log p region
        pts = [(j, y) for j, y in ys if y > math.log(p ** -1.0) - 2 and y < 0]
        if len(pts) < 3:
            pts = ys[: max(3, len(ys) // 2)]
        xs = np.array([j for j, _ in pts]); yv = np.array([y for _, y in pts])
        slope = np.polyfit(xs, yv, 1)[0]
        lam = -slope
        print(f"  {p:5d}  {math.log(p):5.2f}  {lam:6.3f}   {lam*math.log(p)**2:10.2f}    "
              f"{lam:6.3f}")
    print("  => if lambda ~ const across p: true rate is e^{-c k} (beats gpt's crude"
          " e^{-ck/(logp)^2}). If lambda ~ 1/(logp)^2 (col.4 const): gpt bound is tight.")


if __name__ == "__main__":
    check_normalization()
    decay_rate()
