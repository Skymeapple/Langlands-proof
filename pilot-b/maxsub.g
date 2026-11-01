# Maximal subgroups of GSp4(F3) and the characteristic polynomials of their elements.
G := ConformalSymplecticGroup(4,3);;
cp := function(g) return List(CoefficientsOfUnivariatePolynomial(CharacteristicPolynomial(g)), x->IntFFE(x)); end;;
cps := function(H) return Set(List(ConjugacyClasses(H), c->cp(Representative(c)))); end;;
all := cps(G);;
M := List(ConjugacyClassesMaximalSubgroups(G), Representative);;
out := OutputTextFile("maxsub.txt", false);; SetPrintFormattingStatus(out,false);
PrintTo(out, "ALL ", all, "\n");
for H in M do AppendTo(out, "MAX ", Size(H), " ", cps(H), " ", StructureDescription(H), "\n"); od;
CloseStream(out);
QUIT;
