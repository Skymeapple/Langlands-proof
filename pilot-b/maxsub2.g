# Invariants of elements g of GSp4(F3) visible from Frobenius data at a good prime p:
#   [charpoly coeffs low->high, multiplier nu (=p mod 3), dim ker(g-1), dim ker(g+1)]
# dim ker(g-1) = 3-rank of J(F_p);  dim ker(g+1) = 3-rank of the quadratic twist J'(F_p).
G := ConformalSymplecticGroup(4,3);;
J := InvariantBilinearFormUpToScalars(G).matrix;;
one := One(G);;
mult := function(g) local m; m := g*J*TransposedMat(g); return IntFFE(m[1][4]/J[1][4]); end;;
inv := function(g) return [List(CoefficientsOfUnivariatePolynomial(CharacteristicPolynomial(g)), x->IntFFE(x)),
   mult(g), 4 - RankMat(g - one), 4 - RankMat(g + one)]; end;;
invs := function(H) return Set(List(ConjugacyClasses(H), c->inv(Representative(c)))); end;;
all := invs(G);;
M := List(ConjugacyClassesMaximalSubgroups(G), Representative);;
out := OutputTextFile("maxsub2.txt", false);; SetPrintFormattingStatus(out,false);
PrintTo(out, "ALL ", all, "\n");
for H in M do AppendTo(out, "MAX ", Size(H), " ", invs(H), " ", StructureDescription(H), "\n"); od;
CloseStream(out);
Print(Length(all), "\n");
for H in M do Print(Size(H), " ", Length(invs(H)), "\n"); od;
QUIT;
