"""Independently verify the Bernoulli Fourier recursion
  hat mu_{j+1}(xi) = (1/2)[ hat mu_j(xi) + e_p(xi 2^j) hat mu_j(3 xi) ]
and the matrix-contraction prediction for L^2 flattening.
Bernoulli(1/2): each length-k word equally likely; mu_j = law of B_j."""
import numpy as np


def bernoulli_dist_series(p, k):
    """Return list mu[0..k], each a length-p prob vector for B_j under Bernoulli(1/2)."""
    mu = np.zeros(p); mu[0] = 1.0
    series = [mu.copy()]
    c = 1  # 2^j mod p
    idx = np.arange(p)
    for j in range(k):
        tgt = (3 * idx + c) % p          # bit1: b -> (3b+c)
        nxt = 0.5 * mu.copy()
        scat = np.zeros(p)
        scat[tgt] += mu                  # place mass mu[b] at (3b+c)
        nxt += 0.5 * scat
        mu = nxt
        series.append(mu.copy())
        c = (c * 2) % p
    return series


def fourier(mu, p):
    ip = np.outer(np.arange(p), np.arange(p)) % p
    W = np.exp(2j * np.pi * ip / p)
    return W @ mu   # hatmu[xi] = sum_b mu[b] e_p(xi b)


def main():
    p, k = 31, 24
    series = bernoulli_dist_series(p, k)
    # verify recursion at every j, every xi
    maxerr = 0.0
    ep = lambda t: np.exp(2j * np.pi * (t % p) / p)
    for j in range(k):
        hj = fourier(series[j], p)
        hj1 = fourier(series[j + 1], p)
        c = pow(2, j, p)
        for xi in range(p):
            pred = 0.5 * (hj[xi] + ep(xi * c) * hj[(3 * xi) % p])
            maxerr = max(maxerr, abs(pred - hj1[xi]))
    print(f"p={p} k={k}: max |recursion residual| = {maxerr:.2e}  (should be ~0)")

    # L^2 flattening under Bernoulli: sum_{xi!=0} |hatmu_k(xi)|^2 = p*collision - 1
    for kk in [8, 12, 16, 20, 24]:
        s = bernoulli_dist_series(p, kk)
        h = fourier(s[-1], p)
        l2f = float(np.sum(np.abs(h[1:])**2))     # sum over xi!=0
        # matrix-contraction diagnostic: max over xi!=0 of |hatmu_k(xi)|
        worst = float(np.max(np.abs(h[1:])))
        print(f"  k={kk:2d}: sum_{{xi!=0}}|hat|^2={l2f:.3e}  max_xi|hat|={worst:.3e} "
              f"(finite-p diagnostic)")

    # confirm the per-orbit matrix product reproduces the Fourier vector
    print("\nmatrix-contraction check (orbit of xi=1 under mult-by-3):")
    t3 = 1; x = 3 % p
    while x != 1:
        x = (x * 3) % p; t3 += 1
    orbit = [(pow(3, i, p)) % p for i in range(t3)]
    print(f"  ord_p(3)={t3}, orbit size {len(orbit)}")
    # With v_i = hatmu(3^i xi), the recursion reads
    # v'_i = (v_i + phase_i v_{i+1})/2, so P_{i,i+1}=1.
    P = np.roll(np.eye(t3), -1, axis=0)
    Mprod = np.eye(t3, dtype=complex)
    for j in range(k):
        c = pow(2, j, p)
        D = np.diag([ep(orbit[i] * c) for i in range(t3)])
        Mj = 0.5 * (np.eye(t3) + D @ P)
        Mprod = Mj @ Mprod
    vprod = Mprod @ np.ones(t3, dtype=complex)
    h = fourier(series[k], p)
    vtarget = h[orbit]
    vecerr = float(np.max(np.abs(vprod - vtarget)))
    energyerr = abs(float(np.vdot(vprod, vprod).real) -
                    float(np.sum(np.abs(vtarget) ** 2)))
    print(f"  max |product*1 - Fourier orbit| = {vecerr:.2e}")
    print(f"  orbit-energy residual = {energyerr:.2e}")
    assert vecerr < 1e-12
    assert energyerr < 1e-12

    # The top singular value is only a worst-case operator-norm diagnostic;
    # it is not asserted to equal the trajectory from the all-ones vector.
    sv = np.linalg.svd(Mprod, compute_uv=False)[0]
    print(f"  ||prod M_j|| (top singular value, k={k}) = {sv:.3e}")


if __name__ == "__main__":
    main()
