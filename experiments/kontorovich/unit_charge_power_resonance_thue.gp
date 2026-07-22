\\ Exact global Thue solve for the uncorrected h=23 perfect-power rail.
\\
\\ Lean commit f61f569 proves that every such transition must supply an
\\ integer solution of
\\
\\   3^15 X^23 - Y^23 = (A^23-B^23)/F = 5*Phi_23(A,B),
\\
\\ where A=3^114, B=2^154, and F=(A-B)/5.  The right-hand side has
\\ 1,198 decimal digits.  A result is promoted only if the polynomial is
\\ irreducible, the attached tentative class number is one, and `thue`
\\ returns.  PARI documents the default flag-zero algorithm as unconditional
\\ in that class-number-one case; this remains an external PARI trust seam,
\\ not a Lean proof.

default(parisizemax, 16000000000);
A = 3^114;
B = 2^154;
F = (A-B)/5;
K = (A^23-B^23)/F;
P = 3^15*x^23-1;

print("BEGIN_R23 PARI=", version(), " RHS_DIGITS=", #Str(K), " IRREDUCIBLE=", polisirreducible(P));
T = thueinit(P);
print("CLASS=", T[2].no, " REG=", T[2].reg);
S = thue(T, K);
print("SOLUTIONS=", S);
print("R23_DONE");
