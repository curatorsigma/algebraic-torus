# algebraic-torus
`algebraic-torus` is a package that can calculate local ranks of number field tori.
You are also able to work with their character groups.

# Getting started
Use this inside a file in this directory:
```MAGMA
// attach this spec
AttachSpec("main.spec");

// we define a Torus here - the one given by the extension E | F | K
// Here, we assume an involution acting on E | F and get back the Torus SU(E, tau) with this involution
K := QNF();
R<x> := PolynomialRing(K);
F := ext<K | Polynomial([1,1]) : DoLinearExtension:=true>;
E := ext<F | x^2 + 1>;
torus := AlgebraicTorus(K, F, E : Prime:=13);

// we can now calculate local ranks:
// (you can give the place as a prime, infty or an actual PlcNumElt)
rank_at_3 := LocalRank(torus, 3);

// we can also calculate generators of irreducible subtori
// torus has its irreducibles stored in `irreducibles
irred := torus`irreducibles[1];
// We can try to get a generator at specific places
// note that this is not always possible, since good splitting is required for generators to be found
gen := ArbitraryGenerator(irred : set_of_places:=[Decomposition(K, 5)[1][1]]);
// you can also weil-restrict tori, get their realizations and the like

// You can also start with a realized involutive algebra and get an EtaleAlgebra from it
// (which you can use to get its torus, and its ranks)
QQ := TrivialInvolutiveRing(Rationals());
M := MatrixAlgebra(QQ,2);
x := M![0,-1,1,0];
y := M![2,-3,3,2];
N := sub<M | x, y>;
N := InvolutiveAlgebra(N, map<N -> N | x :-> Transpose(x)>);
M2 := MatrixAlgebra(Rationals(), 2);
x2 := M2![0,4, 2,0];
y2 := M2![4,0, 0,4];
N2 := sub<M2 | x2, y2>;
N2 := InvolutiveAlgebra(N2, [Basis(N2)[1], -Basis(N2)[2]]);
A := InvolutiveDirectSum(N, N2);
abstract_algebra, A_to_abstract := EtaleAlgebra(A);
// To make this possible, there is an entire system for star-algebras
// (we call them InvolutiveAlgebra to prevent name-overlap with the
// already provided magma star-algebras)
// Here, QQ is Q as an involutive Ring
// and N is an involutive algebra - an Algebra over an InvolutiveRing with an involution
```
For more examples, you may also take a look at `s_ample_tori/s_ample_tori.m` or `_tests/`

# Naming Conventions
- Normal Variables: `snake_case`
- Attributes of Types: `camelCase`
- Types: `PascalCase`
- Constants: `SCREAMING_SNAKE_CASE`

