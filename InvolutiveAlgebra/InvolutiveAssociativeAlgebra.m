// InvAlgAss and related functions

import "common_functions.m" :
    involutive_algebra_constructor,
    common_involutive_algebra_from_images,
    known_csa,
    common_base_conjugate,
    involution_is_trivial_to_base_ring;

declare attributes AlgAss :
    // the involution as a map on the algebra
    involution,
    // the involutive Ring over which this algebra is an involutive algebra
    // this is usually BaseRing(alg), but it may be BaseRing(...(BaseRing(alg)))
    // e.g. when defining A := M_n(D) with D a skewfield (AlgAss over a Field K)
    // where A is an involutive algebra over K but not necessarily over D
    involutiveBaseRing;


intrinsic InvolutiveAlgebra(alg::AlgAss, inv::Map[AlgAss, AlgAss] :
                            involutive_base_ring:=BaseRing(alg),
                            trivial_base_inv_allowed:=true) -> AlgAss
    {Constructor for an Involutive AlgAss.

    INPUTS
        alg: the algebra to use
        inv: the involution to use
        involutive_base_ring:=BaseRing(alg) :: the involutive base ring
            on which the involution and base involution coincide
        trivial_base_inv_allowed:=true :: when true, automatically add the trivial
            involution to involutive_base_ring if it is not already involutive.
    NOTES
        inv will only be evaluated at Basis(alg | involutive_base_ring), all other values are irrelevant,
        this is so that its easier to check whether inv defines a correct involution.
        Compatibility with the involution on the base ring will be enforced this way.}

    // redirect to the common constructor
    alg, success, msg := involutive_algebra_constructor(
        alg, inv :
        involutive_base_ring:=involutive_base_ring,
        trivial_base_inv_allowed:=trivial_base_inv_allowed);
    // but raise its error from here.
    require success : msg;
    return alg;
end intrinsic;

intrinsic InvolutiveAlgebra(alg::AlgAss, images_of_basis::List :
                            involutive_base_ring:=BaseRing(alg),
                            trivial_base_inv_allowed:=true) -> AlgAss
    {Construct an involutive algebra from the defined images of the basis.

    NOTES
        Creates an involution compatible with the base involution.}

    alg, success, msg := common_involutive_algebra_from_images(
        alg, images_of_basis,
        involutive_base_ring, trivial_base_inv_allowed);
    require success : msg;
    return alg;
end intrinsic;

intrinsic InvolutiveAlgebra(alg::AlgAss, images_of_basis::[AlgAssElt] :
                            trivial_base_inv_allowed:=true) -> AlgAss
    {Construct an involutive algebra from the defined images of the basis.
    Trivial redirect when the recursion depth is one.}

    involutive_base_ring := BaseRing(alg);
    return InvolutiveAlgebra(alg, [*el : el in images_of_basis*] :
                             trivial_base_inv_allowed:=trivial_base_inv_allowed);
end intrinsic;

intrinsic IsInvolutive(alg::AlgAss) -> BoolElt
    {Check whether alg has an involution set.}
    return assigned alg`involution;
end intrinsic;

intrinsic Involution(alg::AlgAss) -> Map[InvAlgAss, InvAlgAss]
    {Get the star associated to this InvAlgAss.}
    require IsInvolutive(alg) : "Algebra has no involution set.";
    return alg`involution;
end intrinsic;

intrinsic _Conjugate(x::AlgAssElt) -> AlgAssElt
    {Apply the involution of Parent(x)}
    require IsInvolutive(Parent(x)) : "The Parent algebra does not have a defined involution.";
    return Parent(x)`involution(x);
end intrinsic;

intrinsic ApplyBaseInvolution(x::AlgAssElt) -> AlgAssElt
    {Apply the involution of BaseRing(Parent(x)) to every entry.}
    return common_base_conjugate(x);
end intrinsic;

intrinsic KnownCSA(alg::AlgAss) -> BoolElt
    {Check whether alg is a central simple algebra.}

    return known_csa(alg);
end intrinsic;

intrinsic InvolutiveBaseRing(alg::AlgAss) -> Rng
    {Return the ring alg is an involutive algebra over.}
    require IsInvolutive(alg) :
        "This algebra is not involutive and so has no involutive base ring.";
    return alg`involutiveBaseRing;
end intrinsic;

intrinsic Kind(alg::AlgAss) -> RngIntElt
    {The kind of this algebra (i.e. "does it restrict to the trivial one on the base ring?")}
    require IsInvolutive(alg) :
        "This algebra is not involutive and has no defined Kind.";
    // the involution on InvolutiveBaseRing(alg) is the same as alg restricted on
    // the embedding along 1 of that ring.
    // The Kind is 2 iff the involution there is not trivial
    return InvolutionIsTrivial(InvolutiveBaseRing(alg)) select 1 else 2;
end intrinsic;

intrinsic InvolutionIsTrivial(alg::AlgAss) -> BoolElt
    {An overload to be consistent with involutive algebras.}
    require IsInvolutive(alg) : "Algebra is not Involutive.";
    if Kind(alg) eq 2 then
        // Kind is 2, so the involution does not even restrict to something trivial
        // in particular, it is not itself trivial
        return false;
    end if;
    // the involution restricts to something trivial on the base ring
    // now the question is whether is acts trivially on Basis(alg | InvolutiveBaseRing(alg))
    return involution_is_trivial_to_base_ring(
        alg`involution, alg, map<alg -> alg | x :-> x>, alg`involutiveBaseRing);
end intrinsic;

intrinsic InvolutiveDirectSum(A::AlgAss, B::AlgAss) -> AlgAss
    {Overload the magma-internal Direct sum, adding the involution to the result if both
    input algebras have an involution set.

    ASSUMES
        that Basis(DirectSum(A, B)) eq Basis(A) + Basis(B) up to the embedding,
        which is correct but the magma docs do not seem to guarantee.}

    require IsInvolutive(A) and IsInvolutive(B) :
        "One of the algebras is not involutive.";

    // now deal with the involutions.
    // it is unclear how we define things when the involutive base rings are different
    // so we do not implement it for now.
    require InvolutiveBaseRing(A) eq InvolutiveBaseRing(B):
        "The two InvolutiveBaseRing s are not equal. Not implemented.";

    // Construct the map given by the direct sum of both involution
    dimB := Dimension(B);
    directsum := DirectSum(A, B);

    inv_on_directsum := map<directsum -> directsum |
                            x :-> directsum !
                                (Eltseq(_Conjugate(A ! [Eltseq(x)[i]
                                                        : i in [1..Dimension(A)]]))
                                 cat Eltseq(_Conjugate(B ! [Eltseq(x)[i]
                                                            : i in [Dimension(A)+1..Dimension(directsum)]])))>;
    // note that we have enforced equality of involutive base rings before.
    directsum := InvolutiveAlgebra(directsum, inv_on_directsum :
                                   involutive_base_ring:=InvolutiveBaseRing(A));
    return directsum;
end intrinsic;

intrinsic Epsilonness(x::AlgAssElt) -> RngIntElt
    {Calculate e such that x is e-hermitian in its involutive parent.

    OUTPUTS
        RngIntElt in \{-1,0,1\} : -1 or 1 if x is e-hermitian. 0 if it is neither.}

    require IsInvolutive(Parent(x)) :
        "Cannot determine Hermitianness in noninvolutive algebra.";
    conj := _Conjugate(x);
    if conj eq x then
        return 1;
    elif conj eq -x then
        return -1;
    else
        return 0;
    end if;
end intrinsic;
