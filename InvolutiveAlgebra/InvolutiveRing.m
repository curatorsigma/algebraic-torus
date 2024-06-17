// Type declaration and functions related to InvRng

import "../core/constants.m" :
    MAX_TESTS_ON_FINITE_RINGS;

declare attributes Rng :
    // Map[Rng, Rng] that makes this Rng a *-Rng
    involution,
    // 1 or 2
    // the natural extension of Kind on CSAs:
    // is 1 iff the involution is trivial
    involutionKind;

/// Check if inv is an involution on a finite ring
///
/// INPUTS
///  Map[FldFin or RngIntRes, FldFin or RngIntRes] inv
/// OUTPUTS
///  BoolElt inv passed all available sanity checks
///  str The reason it didn't pass
/// NOTES
///  Tests are not exhaustive. This function will return false positives
///  but no false negatives
function check_ring_involution_finite_ring(inv)
    R := Domain(inv);
    // test additivity, op-multiplicativity, idempotency
    i := 0;
    while i le MAX_TESTS_ON_FINITE_RINGS do
        i +:= 1;
        x := Random(R);
        if not inv(inv(x)) eq x then
            return false, "The involution is not idempotent.";
        end if;
        j := 0;
        while j le MAX_TESTS_ON_FINITE_RINGS do
            y := Random(R);
            j +:= 1;
            invx := inv(x);
            invy := inv(y);
            if not inv(x + y) eq invx + invy then
                return false, "The involution is not additive.";
            end if;
            if not inv(x*y) eq invy * invx then
                return false, "The involution is not op-multiplicative.";
            end if;
        end while;
    end while;
    return true, "No more tests.";
end function;

/// Check if inv is an involution when it is defined on a NumberField
///
/// INPUTS
///  Map[FldNum, FldNum] inv
/// OUTPUTS
///  BoolElt inv passed all available sanity checks
///  str The reason it didn't pass
/// NOTES
///  Tests are not exhaustive. This function will return false positives
///  but no false negatives
function check_ring_involution_number_field(inv)
    for x in Basis(Domain(inv)) do
        if not inv(inv(x)) eq x then
            return false, "The involution is not idempotent.";
        end if;
        for y in Basis(Domain(inv)) do
            invx := inv(x);
            invy := inv(y);
            if not inv(x + y) eq invx + invy then
                return false, "The involution is not additive.";
            end if;
            if not inv(x*y) eq invy * invx then
                return false, "The involution is not op-multiplicative.";
            end if;
        end for;
    end for;
    return true, "No more tests possible.";
end function;

/// Check if inv is an involution as much as we can
///
/// INPUTS
///  Map[Rng, Rng] inv
/// OUTPUTS
///  BoolElt inv passed all available sanity checks
///  str The reason it didn't pass
/// NOTES
///  Tests are not exhaustive. This function will return false positives
///  but no false negatives
function check_ring_involution_if_possible(inv)
    // test inv(1) eq 1. This can always be checked
    if not IsCoercible(Domain(inv), 1) then
        return false, "Ring is not unital.";
    end if;
    if not inv(Domain(inv) ! 1) eq Domain(inv) ! 1 then
        return false, "inv(1) = 1 is not satisfied.";
    end if;

    if Type(Domain(inv)) in [FldFin, RngIntRes] then
        // For a finite ring we can test everything
        return check_ring_involution_finite_ring(inv);
    elif Type(Domain(inv)) eq FldNum then
        // when the ring is a numberfield, automorphisms must be Q-homomorphisms
        // all other properties can be tested on a basis
        return check_ring_involution_number_field(inv);
    end if;
    return true, "No tests are known for this Ring.";
end function;

/// For known fields, calculate whether inv is trivial
///
/// INPUTS
///  map[Rng, Rng] inv
/// OUTPUTS
///  RngIntElt 1 iff inv is probably trivial, 2 iff it is not trivial
/// IMPLEMENTED FOR the following rings
///  RngInt, FldFin, RngIntRes as well as FldNum and its inheriting structures
///  And RngUPol over these
/// NOTES
///  Not exhaustive for FldFin.
///  This function may return 2, when Domain(inv) is FldFin or RngUPol[FldFin]
///  even if inv is not actually trivial
///  In all other cases, the result is proven if inv is an involution
///  ! But note that it is not possible to check that inv is actually an involution
function get_kind_of_involution(inv)
    R := Domain(inv);
    if Type(R) in [FldFin, RngIntRes] then
        i := 0;
        while i lt MAX_TESTS_ON_FINITE_RINGS do
            i +:= 1;
            x := Random(R);
            if not inv(x) eq x then
                return 2;
            end if;
        end while;
        return 1;
    elif ISA(Type(R), FldNum) then
        L := AbsoluteField(R);
        return inv(L.1) eq L.1 select 1 else 2;
    elif ISA(Type(R), RngUPol) then
        if not inv(R.1) eq R.1 then
            return 2;
        end if;
        inv_on_base := map<BaseRing(R) -> Codomain(inv) | x :-> inv(R!x)>;
        return get_kind_of_involution(inv_on_base);
    elif ISA(Type(R), RngInt) then
        return (inv(R ! 1) eq R ! 1) select 1 else 2;
    end if;

    Type(Domain(inv));
    error "Cannot determine the kind of this involution.";
end function;

intrinsic TrivialInvolutiveRing(ring::Rng) -> Rng
    {Add the trivial involution to ring.}
    ring`involution := map<ring -> ring | r :-> r>;
    ring`involutionKind := 1;
    return ring;
end intrinsic;

intrinsic InvolutiveRing(ring::Rng, inv::Map[Rng, Rng]) -> Rng
    {Basic Constructor for an involutive Ring.}

    require Codomain(inv) eq Domain(inv) :
        "The involution must have equal Domain and Codomain.";
    require ring eq Domain(inv) :
        "The involution must be defined on the given.";

    is_inv, msg := check_ring_involution_if_possible(inv);
    require is_inv: msg;

    ring`involution := inv;
    kind := get_kind_of_involution(inv);
    ring`involutionKind := kind;
    return ring;
end intrinsic;

intrinsic InvolutiveRing(field::FldNum, image_of_generator::FldNumElt) -> Rng
    {Construct the InvRing which is a numberfield with an involution.}
    is_coercible, iofg := IsCoercible(field, image_of_generator);
    require is_coercible :
        "Cannot coerce the generator into the given field.";
    require MinimalPolynomial(field.1) eq MinimalPolynomial(iofg) :
        "The two elements do not have the same minimal polynomial.";

    field`involution := hom<field -> field | iofg>;
    field`involutionKind := iofg eq field.1 select 1 else 2;
    return field;
end intrinsic;

intrinsic InvolutiveRing(image_of_generator::FldNumElt) -> InvRng
    {Construct the InvRing which is a numberfield with an involution.}
    return InvolutiveRing(Parent(image_of_generator), image_of_generator);
end intrinsic;

intrinsic InvolutiveRing(field::FldFin) -> InvRng
    {Assign the only involution of field, if its degree is even.}

    power_of_frob, rem := Quotrem(Degree(field), 2);
    require rem eq 0 : "Only even-degree extensions have nontrivial involutions.";

    field`involution := map<field -> field | x :-> Frobenius(x, power_of_frob)>;
    field`involutionKind := 2;
    return field;
end intrinsic;

intrinsic InvolutiveRing(field::FldCom) -> FldCom
    {Assign the complex conjugation as the involution.}
    field`involution := map<field -> field | x :-> Conjugate(x)>;
    field`involutionKind := 2;
    return field;
end intrinsic;

// checking whether a ring is involutive
intrinsic IsInvolutive(ring::Rng) -> BoolElt
    {Return whether ring has an involution defined.}
    return assigned ring`involution;
end intrinsic;

// working with the involution
intrinsic _Conjugate(x::RngElt) -> RngElt
    {Apply the stored involution if possible.}
    require IsInvolutive(Parent(x)) :
        "The Ring of this element has no assigned involution.";
    return Parent(x)`involution(x);
end intrinsic;

intrinsic Involution(ring::Rng) -> Map[Rng, Rng]
    {Get the assigned involution if available.}
    require assigned ring`involution :
        "This ring has no involution set.";
    return ring`involution;
end intrinsic;

intrinsic Kind(ring::Rng) -> RngIntElt
    {Return the Kind of the involution on ring.}
    require IsInvolutive(ring) : "Ring is not Involutive and therefore has no kind.";
    return ring`involutionKind;
end intrinsic;

intrinsic TypeOfInvolutionOnNormalFormCSA(F::FldRat) -> MonStgElt
    {The trivial involution on Q is of orthogonal type.}
    require IsInvolutive(F) : "Cannot determine the type of a ring which is not involutive.";
    require Kind(F) eq 1 : "Only Involutions of Kind 1 have a well-defined type.";
    return "Orthogonal";
end intrinsic;

intrinsic TypeOfInvolutionOnNormalFormCSA(F::FldNum) -> MonStgElt
    {The Involution on a numberfield - it .}
    require IsInvolutive(F) : "Cannot determine the type of a ring which is not involutive.";
    require Kind(F) eq 1 : "Only Involutions of Kind 1 have a well-defined type.";
    // the trivial Involution is Orthogonal.
    return "Orthogonal";
end intrinsic;

intrinsic InvolutionIsTrivial(ring::Rng) -> BoolElt
    {An overload to be consistent with involutive algebras.}
    require IsInvolutive(ring) : "Ring is not Involutive.";
    return Kind(ring) eq 1;
end intrinsic;

intrinsic Epsilonness(x::RngElt) -> RngIntElt
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
