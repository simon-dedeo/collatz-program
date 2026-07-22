\\ Exact PARI/GP closure of the surviving shortest-recharge power-quine gate.
\\
\\ The homogeneous Thue form attached to
\\
\\   P(x) = 3^15*x^23 - 2^16
\\
\\ is P(X/Y)Y^23 = 3^15*X^23 - 2^16*Y^23.  Hence `thue(T,5)`
\\ enumerates every integer solution of the surviving equation.
\\
\\ PARI's thue documentation states that a flag-zero result is
\\ unconditional when the attached tentative class number is one.  We check
\\ that condition explicitly before accepting the empty solution list.

default(parisizemax, 8000000000);

P = 3^15*x^23 - 2^16;
if (!polisirreducible(P), error("power-quine polynomial is reducible"));

T = thueinit(P);
if (T[2].no != 1, error("fast Thue result is not unconditionally promoted"));

solutions = thue(T, 5);
if (#solutions != 0, error("surviving power-quine equation has a solution"));

print("PARI_VERSION=", version());
print("POLYNOMIAL=", P);
print("IRREDUCIBLE=", polisirreducible(P));
print("TENTATIVE_CLASS_NUMBER=", T[2].no);
print("THUE_RIGHT_HAND_SIDE=5");
print("THUE_SOLUTIONS=", solutions);
print("UNIT_CHARGE_POWER_QUINE_THUE=PASS");
