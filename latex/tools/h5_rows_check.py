#!/usr/bin/env python3
"""Exact rational checks of the primary parameter row (Theorem 1, Section 7) and comparison rows (Appendix C).
Checks the hypotheses of Proposition A.11, the cost gaps, kappa < g_min with the stated slack,
the network-exponent certificates, nu_net = 11, the printed-constants dyadic ceiling, and the root-family bound eps < 1/14."""
from fractions import Fraction as F
from math import factorial
import sys

ok = True
def check(cond, msg):
    global ok
    print(("OK   " if cond else "FAIL ") + msg)
    ok &= bool(cond)

# --- network certificates (Proposition A.2 / Definition A.1) ---
m = 10**6
Wb, sb = 177176569091445000000, 177176569088785861287000000
Wc, sc = 1873807244643542670000, 1873807244636671267308000000
eta_b = F(Wb*m - sb, Wb*m); eta_c = F(Wc*m - sc, Wc*m)
check(eta_b == F(339, 22587335000000), "eta_b = 339/22587335000000")
check(eta_c == F(73, 19906842167500), "eta_c = 73/19906842167500")
check(sum(F(7**j, factorial(j)) for j in range(12)) == F(41438755442, 39916800), "sum_{j<=11} 7^j/j! = 41438755442/39916800")
check(sum(F(7**j, factorial(j)) for j in range(12)) > 1000, "e^7 > 1000, so ln 10^6 < 14")
check(339 * 2**40 == 372734441816064 and 14 * 22587335000000 == 316222690000000 and 339 * 2**40 > 14 * 22587335000000,
      "339*2^40 > 14*22587335000000  (tau = 1-2^-40 certified)")
check(73 * 2**42 == 321057395310592 and 14 * 19906842167500 == 278695790345000 and 73 * 2**42 > 14 * 19906842167500,
      "73*2^42 > 14*19906842167500  (sigma = 1-2^-42 certified)")
check(eta_b > 20 * F(1, 2**50) and eta_c > 20 * F(1, 2**50), "printed tau = sigma = 1-2^-50: both deficits > 20*2^-50")
E = 64 * (Wc + m + 1)**3; B = sc + E
nu_net = next(j for j in range(1, 100) if m**j >= B)
check(nu_net == 11 and m**10 < B < m**11, "nu_net = 11 (m^10 < B_net < m^11)")
check(24 * Wc**3 + 4 * sc + 4 * Wc + 4 < E, "24 W_c^3 + 4 s_c + 4 W_c + 4 < E_net")

# --- rows (primary row in Section 7; secondary and Bluestein comparison rows in Appendix C) ---
xi = F(1, 2**42); zeta = F(1, 2**40); u = F(1, 2**51)
rows = {
 # name: (route, C1, beta, eps, c, tau, sigma, lam, lamp, kappa, expected binding gap, expected slack)
 'Walsh 2^-46 (primary)': ('W', 14, F(1,64), F(1,15), xi/256, 1-4*xi, 1-xi, 1-F(63,64)*xi, 1-F(31,32)*xi, F(1,2**46), F(31,480)*xi, xi/480),
 'Walsh 2^-47':           ('W', 20, F(1,8),  F(1,21), xi/4,   1-4*xi, 1-xi, 1-F(7,8)*xi,   1-F(3,4)*xi,   F(1,2**47), xi/28,  xi/224),
 'Walsh 2^-56 (printed)': ('W', 20, F(1,2),  F(1,21), u/4,    1-2*u,  1-2*u, 1-F(129,128)*u, 1-F(63,64)*u, F(1,2**56), 3*u/64, u/64),
 'Bluestein 2^-182 (printed (38))': ('B', 20, F(1,2), F(1,2**75), F(1,2**56), 1-F(1,2**50), 1-F(1,2**50), 1-F(1,2**52), F(1)-F(1,2**54), F(1,2**182), F(1,2**181), F(1,2**182)),
 'Bluestein 2^-108': ('B', 20, F(1,2), F(1,32), F(1,2**52), 1-F(1,2**50), 1-F(1,2**50), 1-F(1,2**51), 1-F(1,2**52), F(1,2**108), F(1,2**107), F(1,2**108)),
 'Bluestein 2^-85':  ('B', 20, F(15,16), F(1,21), F(7,8)*zeta, 1-zeta, 1-zeta/4, 1-zeta/32, 1-zeta/128, F(1,2**85), zeta**2/24, zeta**2/96),
 'Bluestein 2^-84':  ('B', 14, F(15,16), F(9,128), F(29,32)*zeta, 1-zeta, 1-zeta/4, 1-zeta/32, 1-zeta/128, F(1,2**84), F(261,4096)*zeta**2, 5*F(1,2**92)),
}
for name, (route, C1, beta, eps, c, tau, sigma, lam, lamp, kappa, gexp, sexp) in rows.items():
    print(f"--- {name} ---")
    check(all(x > 0 for x in (beta, eps, c, lam, lamp)) and 0 < tau < 1 and 0 <= sigma < 1 and 0 < beta < 1 and 0 < eps < 1,
          "parameter ranges")
    check(tau in (1 - F(1, 2**40), 1 - F(1, 2**50)) and sigma in (1 - F(1, 2**42), 1 - F(1, 2**50)),
          "tau, sigma among the certified exponents")
    check(max(tau, sigma) < lam < 1, f"max(tau,sigma) < lambda < 1  (margins {lam-tau}, {lam-sigma})")
    check(tau * (1 + c/beta) < lam, f"tau(1+c/beta) < lambda  (margin {lam - tau*(1+c/beta)})")
    check(max(lam, sigma + beta*(1-sigma)) < lamp < 1, f"max(lambda, sigma+beta(1-sigma)) < lambda' < 1")
    check(isinstance(C1, int) and C1 >= nu_net + 3 and eps * C1 < 1, f"C1 = {C1} >= nu_net+3 and eps*C1 < 1 (1-eps*C1 = {1-eps*C1})")
    check(eps * (1 + c) < 1, "eps(1+c) < 1")
    check(eps < F(1, 14), "eps < 1/14 (root family)")
    gaps = {'pre': 1 - eps*(1+c), 'lay': eps*(1-lamp), 'last': eps, 'axis': (1-eps)*(1-tau), 'short': 1-eps}
    if route == 'B':
        gaps['chunk'] = eps * c * (1 - tau)
    gmin = min(gaps.values()); arg = min(gaps, key=gaps.get)
    check(gmin == gexp, f"binding gap g_{arg} = {gmin} (expected {gexp})")
    check(kappa < gmin and gmin - kappa == sexp, f"kappa < g_min with slack {gmin - kappa} (expected {sexp})")
    if name == 'Walsh 2^-56 (printed)':
        check(sigma + beta*(1-sigma) == 1 - u, "printed: sigma+beta(1-sigma) = 1-u")
        ceil = u / 20
        check(ceil == F(8,5) * F(1,2**56) and ceil < F(1, 2**55), "printed ceiling u/20 = (8/5)2^-56 < 2^-55")
        check(gaps['axis'] == F(40,21)*u and gaps['pre'] == (20 - u/4)/21, "printed: g_axis = 40u/21, g_pre = (20-u/4)/21")

# root family constant: 1/2 * 64^(-1/14) > 1/4  <=>  64^(1/14) < 2  <=>  2^6 < 2^14
check(64 < 2**14, "64^(1/14) < 2, so (1/2) 64^(-1/14) > 1/4")
# equal-guard comparisons
check(F(1,2**47) / F(1,2**85) == 2**38 and F(1,2**46) / F(1,2**84) == 2**38, "equal-guard Walsh/Bluestein ratio 2^38")
check(F(1,2**56) / F(1,2**108) == 2**52 and F(1,2**56) / F(1,2**182) == 2**126, "printed Walsh/Bluestein 2^52; vs 2^-182: 2^126")
print("ALL OK" if ok else "SOME CHECKS FAILED")
sys.exit(0 if ok else 1)
