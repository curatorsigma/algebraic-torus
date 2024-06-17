// InvAlgMat and related functions

import "common_functions.m" :
    involutive_algebra_constructor,
    common_involutive_algebra_from_images,
    known_csa,
    basis_to_prime_field,
    common_base_conjugate,
    involution_is_trivial_to_base_ring;

import "../core/primitives.m" :
    decomposition_but_works,
    coordinates_in_basis_fld,
    calculate_fixed_field_raw,
    relative_field_but_does_not_segfault,
    absolutize_place;

declare attributes AlgMat :
    // the involution as a map on the algebra
    involution,
    // the involutive Ring over which this algebra is an involutive algebra
    // this is usually BaseRing(alg), but it may be BaseRing(...(BaseRing(alg)))
    // e.g. when defining A := M_n(D) with D a skewfield (AlgAss over a Field K)
    // where A is an involutive algebra over K but not necessarily over D
    involutiveBaseRing;

intrinsic InvolutiveAlgebra(alg::AlgMat, inv::Map[AlgMat, AlgMat] :
                            involutive_base_ring:=BaseRing(alg),
                            trivial_base_inv_allowed:=true) -> AlgMat
    {Constructor for an Involutive AlgMat.

    INPUTS
        alg: the algebra to use
        inv: the involution to use
        involutive_base_ring:=BaseRing(alg) :: the involutive base ring
            on which the involution and base involution coincide
        trivial_base_inv_allowed:=true :: when true, automatically add the trivial
            involution to involutive_base_ring if it is not already involutive.
    NOTES
        inv will only be evaluated at Basis(alg), all other values are irrelevant,
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

intrinsic InvolutiveAlgebra(alg::AlgMat, images_of_basis::List :
                            involutive_base_ring:=BaseRing(alg),
                            trivial_base_inv_allowed:=true) -> AlgMat
    {Construct an involutive algebra from the defined images of the basis.

    NOTES
        Creates an involution compatible with the base involution.}

    alg, success, msg := common_involutive_algebra_from_images(
        alg, images_of_basis,
        involutive_base_ring, trivial_base_inv_allowed);
    require success : msg;
    return alg;
end intrinsic;

intrinsic InvolutiveAlgebra(alg::AlgMat, images_of_basis::[AlgMatElt] :
                            trivial_base_inv_allowed:=true) -> AlgMat
    {Construct an involutive algebra from the defined images of the basis.
    Trivial redirect when the recursion depth is one.}

    involutive_base_ring := BaseRing(alg);
    return InvolutiveAlgebra(alg, [*el : el in images_of_basis*] :
                             trivial_base_inv_allowed:=trivial_base_inv_allowed);
end intrinsic;

intrinsic IsInvolutive(alg::AlgMat) -> BoolElt
    {Check whether alg has an involution set.}
    return assigned alg`involution;
end intrinsic;

intrinsic Involution(alg::AlgMat) -> Map[InvAlgMat, InvAlgMat]
    {Get the star associated to this InvAlgMat.}
    require IsInvolutive(alg) : "Algebra has no involution set.";
    return alg`involution;
end intrinsic;

intrinsic _Conjugate(x::AlgMatElt) -> AlgMatElt
    {Apply the involution of Parent(x)}
    require IsInvolutive(Parent(x)) : "The Parent algebra does not have a defined involution.";
    return Parent(x)`involution(x);
end intrinsic;

intrinsic ApplyBaseInvolution(x::AlgMatElt) -> AlgMatElt
    {Apply the involution of BaseRing(Parent(x)) to every entry.}
    res := common_base_conjugate(x);
    return res;
end intrinsic;

intrinsic KnownCSA(alg::AlgMat) -> BoolElt
    {Check whether alg is a central simple algebra.}

    return known_csa(alg);
end intrinsic;

intrinsic InvolutiveBaseRing(alg::AlgMat) -> Rng
    {Return the ring alg is an involutive algebra over.}
    require IsInvolutive(alg) :
        "This algebra is not involutive and so has no involutive base ring.";
    return alg`involutiveBaseRing;
end intrinsic;

intrinsic Kind(alg::AlgMat) -> RngIntElt
    {The kind of this algebra (i.e. "does it restrict to the trivial one on the base ring?")}
    require IsInvolutive(alg) :
        "This algebra is not involutive and has no defined Kind.";
    // the involution on InvolutiveBaseRing(alg) is the same as alg restricted on
    // the embedding along 1 of that ring.
    // The Kind is 2 iff the involution there is not trivial
    return InvolutionIsTrivial(InvolutiveBaseRing(alg)) select 1 else 2;
end intrinsic;

intrinsic InvolutionIsTrivial(alg::AlgMat) -> BoolElt
    {An overload to be consistent with involutive algebras.}
    require IsInvolutive(alg) : "Ring is not Involutive.";
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

intrinsic AssociativeAlgebraOfNormalFormCSA(alg::AlgMat)
        -> AlgAss, Map[AlgMat, AlgAss], Map[AlgAss, AlgMat]
    {For a Matrix algebra which is normal form CSA, create an associative
    algebra directly over the base field and the coercion maps in both directions.}

    require alg eq Generic(alg) :
        "Can only get the type in M_n(D) (this is the explicit isomorphism problem).";
    n := Degree(alg);
    D := BaseRing(alg);
    if ISA(Type(D), Alg) then
        K := BaseRing(D);
        // this algebra is M_n(D) with D another algebra
        // enforce D to be a skewfield over a field
        require ISA(Type(K), Fld)
            : "Algebra must be M_n(D) for D a skew field (as AlgAss/AlgMat over a field)";
        dim_of_d_over_k := Dimension(D);
    elif ISA(Type(D), Fld) then
        K := D;
        dim_of_d_over_k := 1;
    else
        require false :
            "The algebra is not in CSA Normal form: The BaseRing is neither Alg nor Fld.";
    end if;


    // the basis element dij of the new algebra is D_d * E_(ij) where
    // the D_d are Basis(BaseRing(alg))
    // and the E_(ij) are MatrixUnits(alg, i, j)
    new_basis := [(alg ! Basis(D)[d]) * MatrixUnit(alg, i, j) :
                  d in [1..dim_of_d_over_k],  i in [1..n], j in [1..n]];

    // D_d1 E_(ij) * D_d2 E_(jl) = D_d1 * D_d2 * E_(il)
    // which then has to be decomposed by a basis of D | K
    basis := [[[(j eq k and x eq i and y eq l)
            select Eltseq(Basis(D)[d1] * Basis(D)[d2])[d3]
            else K ! 0
           // The index at which we take the component first*second basis element.
           : d3 in [1..dim_of_d_over_k],  x in [1..n], y in [1..n]]
          // The index of the second basis element
          : d2 in [1..dim_of_d_over_k],  k in [1..n], l in [1..n]]
         // the index of the first basis element
         : d1 in [1..dim_of_d_over_k],  i in [1..n], j in [1..n]];
    A := AssociativeAlgebra<K, dim_of_d_over_k * n^2 |
        basis>;

    alg_to_A := map<
        alg -> A |
        x :-> A ! [Eltseq(x[i][j])[d]
                   : d in [1..dim_of_d_over_k],  i in [1..n], j in [1..n]]>;
    A_to_alg := map<
        A -> alg |
        x :-> &+[Eltseq(x)[i] * new_basis[i] : i in [1..Dimension(A)]]>;

    return A, alg_to_A, A_to_alg;
end intrinsic;

intrinsic TypeOfInvolutionOnNormalFormCSA(alg::AlgMat) -> MonStgElt
    {Calculate the Type of involution on this algebra which must be in CSA normal form,
    i.e. alg = M_n(D) with D a skewfield over a field or a field.}

    require IsInvolutive(alg) :
        "Can only get the type for an involutive Algebra.";
    require alg eq Generic(alg) :
        "Can only get the type in M_n(D) (this is the explicit isomorphism problem).";

    n := Degree(alg);
    D := BaseRing(alg);
    K := InvolutiveBaseRing(alg);
    require IsInvolutive(K) :
        "The InvolutiveBaseRing of the Algebra must be involutive.";

    if ISA(Type(D), Fld) then
        require K eq D :
            "The BaseRing must be the InvolutiveBaseRing if it is a field.";
        // this algebra is M_n(D) with D a field
        is_full_matrices_over_field := true;
    elif ISA(Type(D), Alg) then
        // this algebra is M_n(D) with D another algebra
        // enforce D to be a skewfield over a field
        require K eq BaseRing(D) :
            "InvolutiveBaseRing must be BaseRing(BaseRing(alg)) if it is not BaseRing(alg).";
        require ISA(Type(K), Fld)
            : "Algebra must be M_n(D) for D a skew field (as AlgAss/AlgMat over a field) or field";
        require IsInvolutive(K)
            : "The Field over which the Algebra is defined must be involutive.";
        is_full_matrices_over_field := false;
    else
        ExtendedType(D);
        error "The BaseRing must be Fld, AlgAss, or AlgMat";
    end if;

    require Degree(K, PrimeField(K)) lt Infinity() :
        "The Algebra must be defined over a field which is a finite extension of its prime field.";

    require Kind(alg) eq 1 :
        "Only involutions of the first kind have well-defined type.";

    require not Characteristic(K) eq 2 :
        "Algorithms for characteristic 2 are currently not implemented.";

    // we now know we are in a csa of normal form we can work in
    if is_full_matrices_over_field then
        // the symetric (i.e. the symmetrized since char != 2) part of alg
        alg_forgetful, iota := VectorSpace(alg);
        symd := sub<alg_forgetful | [iota(x + _Conjugate(x)) : x in Basis(alg)]>;
        if Dimension(symd) eq Integers() ! n * (n + 1) / 2 then
            return "Orthogonal";
        else
            // The type must be symplectic or Orthogonal. Assert this.
            // other dimensions are impossible by the theory
            assert Dimension(symd) eq Integers() ! n * (n - 1) / 2;
            return "Symplectic";
        end if;
    end if;

    // this is M_n(D), D is a nontrivial division algebra over K with K as its center.
    // this is a bit trickier: redefine A as an associative algebra over K directly
    // and calculate the symmetrized part there
    A, alg_to_A, A_to_alg := AssociativeAlgebraOfNormalFormCSA(alg);

    // now push the involution forward to A
    // BaseRing(A) is already involutive, this was required earlier
    A := InvolutiveAlgebra(A, A_to_alg * Involution(alg) * alg_to_A);

    // calculate the symmetrized part in A
    symd := sub<A | [x + _Conjugate(x) : x in Basis(A)]>;
    if Dimension(symd) eq Integers() ! n * (n + 1) / 2 then
        return "Orthogonal";
    else
        // The type must be symplectic or Orthogonal. Assert this.
        // other dimensions are impossible by the theory
        assert Dimension(symd) eq Integers() ! n * (n - 1) / 2;
        return "Symplectic";
    end if;
end intrinsic;

// conversion from and to forms for CSAs
intrinsic InvolutiveAlgebra(B::AlgMatElt) -> AlgMat
    {Given an eps-hermitian form on D^n, construct M_n(D) with the adjoint involution.

    Here, D must be a central division algebra and the result will be CSA over Center(D).
    NOTES:
        The matrix B defines the form (x, y) :-> bar(x)^T * B * y
        i.e. linear in the second component (from the right)

        This is essentially calculating [KMRT, 4.1]}

    alg := Parent(B);
    require alg eq Generic(alg) :
        "The Parent of the form must be a full matrix algebra.";
    require IsInvolutive(alg) : "Parent(B) must be involutive.";
    D := BaseRing(alg);
    try
        is_div_ring := IsDivisionRing(D);
    catch e
        require false :
            "The BaseRing of the Parent of the form must be a known division ring.";
    end try;
    require is_div_ring :
        "The BaseRing of the Parent of the form must be a known division ring.";

    if ISA(Type(D), Fld) then
        // this algebra is M_n(D) with D a field
        K := D;
    elif ISA(Type(D), Alg) then
        // this algebra is M_n(D) with D another algebra
        // enforce D to be a skewfield over a field
        K := BaseRing(D);
        require ISA(Type(K), Fld)
            : "Algebra must be M_n(D) for D a skew field (as AlgAss/AlgMat over a field) or field";
        require IsInvolutive(K)
            : "The Field over which the Algebra is defined must be involutive.";
    else
        ExtendedType(D);
        error "The BaseRing must be Fld, AlgAss, or AlgMat";
    end if;

    // we do not want to override the involution but create a new algebra
    // so we make a hard copy here (this has to call New(MatAlg), which MatrixAlgebra(D, n) does not do)
    alg_copy := sub<alg | alg>;
    is_coercible, B_copy := IsCoercible(alg_copy, B);
    assert is_coercible;
    alg_copy := InvolutiveAlgebra(
        alg_copy, map<alg_copy -> alg_copy | x :-> alg_copy ! _Conjugate(alg ! x)>);

    theta_B_transpose := Transpose(ApplyBaseInvolution(B_copy));
    theta_B_transpose_inv := theta_B_transpose^(-1);
    involution := map<
        alg_copy -> alg_copy |
        x :-> theta_B_transpose_inv * Transpose(ApplyBaseInvolution(x)) * theta_B_transpose>;

    if GetAssertions() ge 2 then
        for a in Basis(alg_copy) do
            inva := involution(a);
            assert B * a eq ApplyBaseInvolution(Transpose(inva)) * B;
            assert involution(inva) eq a;
        end for;
    end if;

    alg_copy := InvolutiveAlgebra(alg_copy, involution : involutive_base_ring:=K);

    return alg_copy;
end intrinsic;

/// Internal
/// this is the conversion from the solution space to the Matrix algebra
function solution_of_form_equations_to_element(b, alg, D, K, f_basis_of_k, n)
    dim_of_d_over_k := (D cmpeq K) select 1 else Dimension(D);
    q_sequence := Eltseq(b);
    q_sequence := [&+[&+[q_sequence[(delta - 1) * Dimension(alg) + index +
                                    (findex - 1) * Dimension(alg) * dim_of_d_over_k]
                            * f_basis_of_k[findex]
                         : findex in [1..#f_basis_of_k]] * Basis(D)[delta]
                      : delta in [1..dim_of_d_over_k]]
                   : index in [1..Dimension(alg)]];
    M := MatrixAlgebra(D, n);
    M := sub<M | M>;
    M := InvolutiveAlgebra(
        M,
        map<M -> M |
            x :-> [_Conjugate(Eltseq(Transpose(x))[j]) : j in [1..Dimension(M)]]>);
    B := Transpose(M ! q_sequence);
    return B;
end function;

/// Internal:
/// Get the equations that have to be satisfied while converting an involution
/// to the "adjoint" form;
/// only the equations needed for adjointness to the involution
///  (not for hermitianness)
/// and only when alg is defined over a field K
function form_equations_base_is_field(alg, K)
    f_basis_of_k, F := basis_to_prime_field(K);
    n := Degree(alg);

    list_of_equations_to_satisfy := [];
    for i in [1..n] do
        for j in [1..n] do
            // write out all the equations given by
            // B * E_ij = theta(tau(E_ij)^T) * B,       (*)

            eij := MatrixUnit(alg, i, j);
            // theta(tau(E_ij)^T)
            theta_tau_eij_transpose := ApplyBaseInvolution(Transpose(_Conjugate(eij)));

            list_of_equations_to_satisfy cat:= [
                // coming from the lhs of (*)
                [f_basis_of_k[findex] *
                    /*(findex ne 1) select 0 else*/
                 K ! ((j eq m and row eq k and col eq i) select (-1) else 0) +
                 // coming from the rhs of (*)
                 K ! ((col eq m) select theta_tau_eij_transpose[k][row] else 0)
                    // row and col are the row and column of B respectively
                    : row in [1..n], col in [1..n], findex in [1..#f_basis_of_k]] :
                // the condition is one on matrices. for each pair (k,m) we enforce
                // the (k,m)-Part of the equation (*) separately
                k in [1..n], m in [1..n]
            ];
        end for;
    end for;
    return list_of_equations_to_satisfy;
end function;

/// Internal:
/// write out all the equations given by
/// B * D[delta] * E_ij = theta(tau(D[delta] * E_ij)^T) * B,       (*)
/// only where alg is defined over the skew field D
function equations_from_one_test_skewfield(alg, D, K, F, f_basis_of_k, i, j, delta, n)
    eij := MatrixUnit(alg, i, j);
    // theta^~(tau(D[delta] * E_ij)^T)
    // NOTE: this is not ApplyBaseInvolution(_Conjugate(D[delta] * E_ij)^T),
    // because the base involution is of alg as a CSA over K
    // we need the involution of D on alg as End_D(D^n) here, which we calculate here
    theta_tau_eij_transpose := &+[
        alg ! _Conjugate(Eltseq(Transpose(
            _Conjugate((alg ! Basis(D)[delta]) * eij)))[algindex])
        * Basis(alg)[algindex]
        : algindex in [1..Dimension(alg)]];

    res := [
        [// coming from the lhs of (*)
         - F ! ((m eq j and row eq k and col eq i) select
            coordinates_in_basis_fld(
                Eltseq(Basis(D)[gamma] * Basis(D)[delta])[omega]
                 * f_basis_of_k[findex],
                f_basis_of_k)[f0]
            else 0) +
         // coming from the rhs of (*)
         F ! ((col eq m) select
            coordinates_in_basis_fld(
              // This is the part of theta(tau(D[delta]) * eij)^T
              // belonging to the omega-th Basis element of D|K
              Eltseq(theta_tau_eij_transpose[k][row] * Basis(D)[gamma])[omega]
               * f_basis_of_k[findex],
              f_basis_of_k)[f0]
            else 0)
         // row and col are the row and column of B respectively
         : row in [1..n], col in [1..n], gamma in [1..Dimension(D)],
             // for the hermitian-rescaling we need to be on the level of the field
             // in this function, findex is only used for consistency of the equations
             findex in [1..#f_basis_of_k]] :
        // the condition is one on matrices. for each pair (k,m) we enforce
        // the f0 entry of the omega-Entry of D
        // of the (k,m)-Part of the equation (*) separately
        k in [1..n], m in [1..n], omega in [1..Dimension(D)], f0 in [1..#f_basis_of_k]
    ];
    return res;
end function;

/// Write out all the equations the entries of the form have to satisfy
///
/// INPUTS
///  AlgMat alg: parent Algebra, M_n(D), defined over a Skewfield
///  Alg D : BaseRing(alg), a skewfield over K
///  Fld K : the field over which alg is CSA
///  RngIntElt n : Degree(alg)
/// OUTPUTS
///  List[Equations]
/// NOTES
///  A solution of the equations will give coefficients over K for the form
///  The coefficients for B[i][j] will be in
///  res[(i - 1) * n * d + (j - 1) * d + 1] till res[(i - 1) * n * d + j * d]
///  as elements of K, yielding the element of D with the basis of D.
function form_equations_base_is_skewfield(alg, D, K, n)

    f_basis_of_k, F := basis_to_prime_field(K);

    list_of_equations_to_satisfy := [];
    for i in [1..n] do
        for j in [1..n] do
            new_eqs := [];
            for delta in [1..Dimension(D)] do
                list_of_equations_to_satisfy cat:= equations_from_one_test_skewfield(
                    alg, D, K, F, f_basis_of_k, i, j, delta, n);
            end for;
        end for;
    end for;
    return list_of_equations_to_satisfy;
end function;

function form_equations(alg, D, K, n)
    if D cmpeq K then
        return form_equations_base_is_field(alg, D);
    else
        return form_equations_base_is_skewfield(alg, D, K, n);
    end if;
end function;

intrinsic GetFormOfInvolution(alg::AlgMat) -> AlgMatElt
    {Get a hermitian form corresponding to this involution.

    The result is a Matrix B in M_r(D) defining a form b(x, y) := theta(x^T) * B * y
    where theta is the involution on BaseRing(alg) =: D and x, y in D^r.

    The resulting form satisfies b(x, a * y) eq b(inv(a) * x, y) for a in alg, x, y in D^r.

    This function only works when alg = M_r(D) for D := BaseRing(alg) and alg is CSA.

    Algorithm: own, using the statements from
        - [KMRT, 2.6] : types and dimensions of Symd
        - [KMRT, 4.2] : The 1:1 correspondence
            Their M is our D^r
            Their E is our D
            Their F is our K
            Their theta is our Involution(D)}

    require IsInvolutive(alg) :
        "Can only get the form for an involutive Algebra.";
    require alg eq Generic(alg) :
        "Can only get the form in M_n(D) (this is the explicit isomorphism problem).";

    n := Degree(alg);
    D := BaseRing(alg);
    K := InvolutiveBaseRing(alg);
    require IsInvolutive(K) :
        "The InvolutiveBaseRing of the Algebra must be involutive.";

    if ISA(Type(D), Fld) then
        require K eq D :
            "The BaseRing must be the InvolutiveBaseRing if it is a field.";
        // this algebra is M_n(D) with D a field
        is_full_matrices_over_field := true;
    elif ISA(Type(D), Alg) then
        // this algebra is M_n(D) with D another algebra
        // enforce D to be a skewfield over a field
        require K eq BaseRing(D) :
            "InvolutiveBaseRing must be BaseRing(BaseRing(alg)) if it is not BaseRing(alg).";
        require ISA(Type(K), Fld)
            : "Algebra must be M_n(D) for D a skew field (as AlgAss/AlgMat over a field) or field";
        require IsInvolutive(K)
            : "The Field over which the Algebra is defined must be involutive.";
        is_full_matrices_over_field := false;
    else
        ExtendedType(D);
        error "The BaseRing must be Fld, AlgAss, or AlgMat";
    end if;

    require Degree(K, PrimeField(K)) lt Infinity() :
        "The Algebra must be defined over a field which is a finite extension of its prime field.";

    // the trivial case
    if n eq 0 then
        return alg ! 1;
    end if;

    // the equations the entries of B will have to satisfy
    // for the defining property b(x, ay) = b(tau(a)x, y) to hold
    list_of_equations_to_satisfy := form_equations(alg, D, K, n);


    // this kernel contains all matrices that correspond to the involution tau
    // i.e. the Bs such that for all F:
    // x^T*B*F*y = x^T * tau(F)^T * B * y
    // holds
    m := Matrix(list_of_equations_to_satisfy);
    ker := Kernel(Transpose(m));
    assert Dimension(ker) ge 1;

    // get abasis to the prime field of K
    f_basis_of_k, _ := basis_to_prime_field(K);

    // regroup the elements of K into single elements of D
    B := solution_of_form_equations_to_element(
        Basis(ker)[1], alg, D, K, f_basis_of_k, n);


    // check if the result is correct
    if GetAssertions() ge 1 then
        for a in Basis(alg) do
            inva := _Conjugate(a);

            // Note: we do not need to check against ApplyBaseInvolution, but against the involution of D applied
            // to each element of M_n(D) here, which the rhs calculates
            assert B * a eq
                &+[_Conjugate(Eltseq(Transpose(inva))[algindex]) * Basis(alg)[algindex]
                   : algindex in [1..Dimension(alg)]] * B;
        end for;
    end if;


    // Calculate the epsilonness so we can guarantee that B is (skew-)hermitian
    kind := Kind(D);
    if kind eq 1 then
        type := TypeOfInvolutionOnNormalFormCSA(alg);
        type_on_base := TypeOfInvolutionOnNormalFormCSA(D);
        if type eq type_on_base then
            eps := 1;
        else
            eps := -1;
        end if;
    elif kind eq 2 then
        // skew-hermitian and hermitian would both work
        // but we would rather use hermitian forms then skew-hermitian ones
        eps := 1;
    end if;
    // now hermitianise B (so that it is either herm or skew-herm)
    B := B + eps * _Conjugate(B);

    // for sanity check: the dimension of the kernel should be...
    // the form is unique up to multiplication by a factor in K fixed under
    // the involution on D. this is an Aut of K of order kind, which is where
    // this formula comes from
    dimension_should_be := Integers() ! (#f_basis_of_k / kind);

    assert2 Epsilonness(B) eq eps;
    assert2 IsInvolutive(Parent(B));

    return B;
end intrinsic;

intrinsic InvolutiveDirectSum(A::AlgMat, B::AlgMat) -> AlgMat
    {Overload the magma-internal Direct sum, adding the involution to the result if both
    input algebras have an involution set.

    ASSUMES
        that Basis(DirectSum(A, B)) eq Basis(A) + Basis(B) up to the embedding,
        which is correct but the magma docs do not seem to guarantee.}
    directsum := DirectSum(A, B);

    require IsInvolutive(A) and IsInvolutive(B) :
        "One of the algebras is not involutive.";

    // now deal with the involutions.
    // it is unclear how we define things when the involutive base rings are different
    // so we do not implement it for now.
    require InvolutiveBaseRing(A) eq InvolutiveBaseRing(B):
        "The two InvolutiveBaseRing s are not equal. Not implemented.";

    // Construct the map given by the direct sum of both involution
    nA := Degree(A);
    nB := Degree(B);
    inv_on_directsum := map<directsum -> directsum |
                            x :-> DirectSum(_Conjugate(A ! Submatrix(x,1,1,nA,nA)),
                                            _Conjugate(B ! Submatrix(x,1+nA,1+nA,nB,nB)))>;
    // note that we have enforced equality of involutive base rings before.
    directsum := InvolutiveAlgebra(directsum, inv_on_directsum :
                                   involutive_base_ring:=InvolutiveBaseRing(A));
    return directsum;
end intrinsic;

intrinsic Epsilonness(x::AlgMatElt) -> RngIntElt
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


/////////////////////////////////////////////
// Calculating local ranks of SU(M_n(K), tau)
/////////////////////////////////////////////
// This requires lots of helper functions. The main function is LocalRankOfSU.
// This entire section, with some of the helper functions, relies on
// [PRZEMYSŁAW KOPROWSKI AND ALFRED CZOGAŁA.
//  COMPUTING WITH QUADRATIC FORMS OVER NUMBER FIELDS;
//  arXiv:1304.0708v2 [math.NT]]


/// Calculate the restriction of the C-Form q to an R-Form of twice the dimension
///
/// INPUTS
///  C-Matrix q: The C-Form
/// OUTPUTS
///  R-Matrix q_res twice the dimension of q that defines the R-Form on the R-Basis {1, i} of C
/// ASSUMPTIONS
///  The underlying involution is assumed to be the complex conjugation
function restriction_of_C_form_to_R(q)
    n := NumberOfRows(q);
    precision := Precision(Parent(q[1][1]));
    CC := ComplexField(precision);
    RR_basis_of_CC := [CC ! 1, CC.1];

    q_res_coeffs := [];
    // now calculate q(b, c) for b, c in the K-Basis of L^n
    for i in [1..n], bind in [1..2] do
        Append(~q_res_coeffs, []);
        for j in [1..n], cind in [1..2] do
            Append(~q_res_coeffs[(i - 1) * 2 + bind],
                   Re(q[i][j] * Conjugate(RR_basis_of_CC[bind]) * RR_basis_of_CC[cind]));
        end for;
    end for;
    return Matrix(RealField(precision), q_res_coeffs);
end function;

/// Calculate the restriction of the L-Form q to a K-Form where [L:K] = 2
///
/// GIVEN
///  - AlgMatElt q
/// WHERE
///  - L := BaseRing(Parent(q)) is FldNum
///  - K := BaseField(L), Degree(L, K) eq 2
///  - IsInvolutive(L) and K is fixed by the involution
/// CALCULATE
///  - An AlgMatElt twice the size of q that defines the K-Form on a K-Basis
///      {1, a} of L such that a^2 \in K and a -> -a under the involution
function restriction_of_L_form_to_K(q)
    L := BaseRing(Parent(q));
    assert ISA(Type(L), FldNum);
    assert IsInvolutive(L);
    K := BaseRing(L);
    assert Degree(L, K) eq 2;
    assert _Conjugate(L ! K.1) eq L ! K.1;

    n := NumberOfRows(q);
    // find a such that L = K(a) and a^2 in K and a -> -a under the involution
    // Algorithm stolen from
    // https://math.stackexchange.com/questions/2494309/field-extension-with-degree-2
    coeffs := Coefficients(DefiningPolynomial(L));
    assert3 forall{c : c in coeffs | _Conjugate(L ! c) eq L ! c};
    assert #coeffs eq 3;
    // DefiningPolynomial should return a normed polynomial
    assert coeffs[3] eq 1;
    // We have L.1^2 + coeffs[2] * L.1 + coeffs[1] = 0
    alpha := L.1 + coeffs[2] / 2;
    // thus, we have alpha^2 = L.1^2 + L.1 * coeffs[2] + coeffs[2]^2 = coeffs[2]^2 - coeffs[1] in K
    // in addition, the two solutions to this K-defined polynomial are [alpha, -alpha] and thus
    // _Conjugate(alpha) == - alpha must hold
    assert _Conjugate(alpha) eq -alpha;
    K_basis_of_L := [L ! 1, alpha];
    involution_on_K_basis_of_L := [L ! 1, - alpha];

    q_res_coeffs := [];
    // now calculate q(b, c) for b, c in the K-Basis of L^n
    for i in [1..n], bind in [1..2] do
        Append(~q_res_coeffs, []);
        for j in [1..n], cind in [1..2] do
            Append(~q_res_coeffs[(i - 1) * 2 + bind],
                   coordinates_in_basis_fld(
                        q[i][j] * involution_on_K_basis_of_L[bind] * K_basis_of_L[cind],
                        K_basis_of_L)[1]);
        end for;
    end for;
    return Matrix(K, q_res_coeffs);
end function;

/// Check if q is hyperbolic at the relevant place
///
/// INPUTS
///      Matrix[FldNum] q: The Quadratic form
///      finite place of K place_in_extension: the place to check
///      FldNumElt disc=false: discriminant of q, if already known
/// OUTPUTS
///      BoolElt: true if the form is hyperbolic at the place, false otherwise
function is_hyperbolic(q, place_in_extension : disc:=false)
    if not IsEven(NumberOfRows(q)) then
        return false;
    end if;

    K := NumberField(place_in_extension);

    // if required, recalculate the discriminant
    if disc cmpeq false then
        dim_q := NumberOfRows(q);
        quot, r := Quotrem(dim_q * (dim_q - 1), 4);
        disc := ((r eq 0) select 1 else -1) * Determinant(q);
    end if;

    K_abs, iota_K_K_abs, P_abs := absolutize_place(K, place_in_extension);
    disc := iota_K_K_abs(disc);
    Kp, iota := Completion(K_abs, P_abs);
    if not IsSquare(iota(disc)) then
        return false;
    end if;

    m := NumberOfRows(q) / 2;
    diag := Diagonalization(q);
    hasse_invariant := &*[HilbertSymbol(K_abs ! diag[i][i], K_abs ! diag[j][j], Ideal(P_abs)) : i in [1..2*m], j in [1..2*m] | i lt j];
    hilbert_symbol := HilbertSymbol(K_abs ! -1, K_abs ! -1, Ideal(P_abs))^(m * (m-1)/2);

    return hasse_invariant eq hilbert_symbol;
end function;

/// for a symmetric form q over K calculate ind(q x K_P)
///
///  INPUTS
///      nxn K-matrix q
///      PlcNumElt P in K
///  OUTPUTS
///      RngIntElt ind(q x K_P)
///  ALGORITHM
///      Algorithm 8 of
///      [PRZEMYSŁAW KOPROWSKI AND ALFRED CZOGAŁ􏰀A.
///       COMPUTING WITH QUADRATIC FORMS OVER NUMBER FIELDS;
///       arXiv:1304.0708v2 [math.NT]]
function local_witt_index_K_place(q, P)
    assert IsSymmetric(q);

    K := NumberField(P);
    M := BaseRing(Parent(q));

    dim_q := NumberOfRows(q);
    quot, r := Quotrem(dim_q * (dim_q - 1), 4);
    disc := ((r eq 0) select 1 else -1) * Determinant(q);

    if IsInfinite(P) then
        // infinite place correspond to Q-Embeddings into C
        q_embed := Matrix([[Evaluate(q[i][j], P) : j in [1..dim_q]] : i in [1..dim_q]]);
        if not IsReal(P) then
            // for the properly complex places we need the restriction again.
            // this doubles the dimension, but makes the form real for OrthogonalizeGram to work
            q_res := restriction_of_C_form_to_R(q_embed);
            // Calculate the R-index of q_res
            d := OrthogonalizeGram(q_res);
            n_plus := #[j : j in [1..NumberOfRows(q)] | d[j][j] gt 0];
            n_minus := #[j : j in [1..NumberOfRows(q)] | d[j][j] lt 0];
            // but divide by two, since we have doubled the dimension
            // while redefining over R
            return Minimum(n_plus, n_minus) / 2;
        end if;
        // Calculate the R-index of q
        d := OrthogonalizeGram(q_embed);
        n_plus := #[j : j in [1..NumberOfRows(q)] | d[j][j] gt 0];
        n_minus := #[j : j in [1..NumberOfRows(q)] | d[j][j] lt 0];
        return Minimum(n_plus, n_minus);
    end if;

    // P is a finite place
    K_abs, iota_K_K_abs, P_abs := absolutize_place(K, P);
    KP, iota_KP := Completion(K_abs, P_abs);
    disc := iota_K_K_abs(disc);
    if IsEven(dim_q) then
        // printf "Index at place %o:\n", P_K_tup, "Minimal";
        if is_hyperbolic(q, P : disc:=disc) then
            // printf "Form is hyperbolic at this place. Index %o.\n", dim_q / 2, "Minimal";
            return Floor(dim_q / 2);
        end if;
        // nota bene: IsSquare works without precision errors in pAdic fields
        if IsSquare(iota_KP(disc)) then
            // printf "Form is not hyperbolic, but discriminant is locally square. Index %o.\n", (dim_q - 4) / 2, "Minimal";
            return Floor((dim_q - 4) / 2);
        else
            // printf "Form is not hyperbolic, discriminant is not locally square. Index %o.\n", (dim_q - 2) / 2, "Minimal";
            return Floor((dim_q - 2) / 2);
        end if;
    else
        // psi := phi \orth (-1)^(d*(d+1)/2) * det(phi))
        psi := DiagonalJoin(q, Matrix(M, [[M ! disc * (-1)^dim_q]]));
        disc_psi := Determinant(q)^2;
        if is_hyperbolic(psi, P : disc:=disc_psi) then
            return Floor((dim_q - 1) / 2);
        else
            return Floor((dim_q - 3) / 2);
        end if;
    end if;
end function;

/// Calculate sum_P|p ind(q x K_P)
///
///  INPUTS
///      AlgMatElt q: the Form on L^n (as element of M_n(L))
///      PlcNumElt p: place of a subfield of L
///      AlgMat alg: the involutive Algebra M_n(L)
///  OUTPUTS
///      RngIntElt sum_P|p ind(q x K_P)
function local_witt_index_single_place_in_F(q, p)
    alg_tmp := Parent(q);
    assert IsInvolutive(alg_tmp);
    assert ISA(Type(p), PlcNumElt);

    L_tmp := BaseRing(alg_tmp);
    // image of L.1 under the involution of alg_tmp:
    // (it is again scalar by the theory of involutions - simply take the first diagonal entry)
    image_of_L_tmp1 := _Conjugate(alg_tmp ! L_tmp.1)[1][1];
    K_tmp := calculate_fixed_field_raw(L_tmp, image_of_L_tmp1);

    // We want the field stack to look this way:
    // L | K | NumberField(p), with q having values in L
    F := NumberField(p);
    K, K_tmp_to_K := relative_field_but_does_not_segfault(F, K_tmp);
    K := InvolutiveRing(K.1);
    L, L_tmp_to_L := relative_field_but_does_not_segfault(K, L_tmp);
    image_of_L1 := L_tmp_to_L(_Conjugate(alg_tmp ! Inverse(L_tmp_to_L)(L.1))[1][1]);
    assert Evaluate(DefiningPolynomial(L), image_of_L1) eq 0;
    L := InvolutiveRing(image_of_L1);

    // now redefine q
    alg := MatrixAlgebra(L, NumberOfRows(q));
    alg := sub<alg | alg>;

    alg := InvolutiveAlgebra(alg, map<alg -> alg | x :-> alg ! _Conjugate(alg_tmp ! x)>);
    q := alg ! q;

    if Degree(L, Rationals()) eq Degree(K, Rationals()) then
        // L = K
        if IsSymmetric(q) then
            // form is symmetric. Calculate its index locally
            return &+[local_witt_index_K_place(q, P[1])
                      : P in decomposition_but_works(K, p)];
        end if;
        // form is skew-symmetric. Its index is half the dimension
        return NumberOfRows(q) / 2 * #decomposition_but_works(K, p);
    end if;


    // [L:K] = 2
    assert AbsoluteDegree(L) eq 2 * AbsoluteDegree(K);
    rank := 0;
    for P_K_tup in decomposition_but_works(K, p) do
        decomp_in_L := decomposition_but_works(L, P_K_tup[1]);
        if #decomp_in_L eq 1 then
            // there is only a single place in L over P in K
            // [L_P : K_P] = 2 and q x K_w is still properly eps-hermitian wrt the involution of L_P|K_P
            if Epsilonness(q) eq 1 then
                q_res := restriction_of_L_form_to_K(q);
                assert IsSymmetric(q_res);
                r := local_witt_index_K_place(q_res, P_K_tup[1]);
                assert IsEven(r);
                rank +:=  Integers() ! (r / 2);
                continue P_K_tup;
            end if;
            // Form is skew-hermitian. L.1 * q is hermitian and the indices are equal
            q_herm := L.1 * q;
            assert2 Epsilonness(q) eq 1;

            q_res := restriction_of_L_form_to_K(q_herm);
            assert IsSymmetric(q_res);
            r := local_witt_index_K_place(q_res, P_K_tup[1]);
            assert IsEven(r);

            rank +:= Integers() ! (r / 2);
            continue P_K_tup;
        end if;
        // There are two places in L over K
        rank +:= NumberOfRows(q) - 1;
    end for;
    // we were in the case [L:K] = 2 and went through the for loop.
    return rank;
end function;

intrinsic LocalRankOfSU(alg::AlgMat, place::PlcNumElt) -> RngIntElt
    {Given an involutive Matrix Algebra of the form M_n(K) and a place in F,
    calculate rk_place(SU(M_n(K), involution)).

    Here F is a subfield of the fixed field of K under the involution
    Currently only implemented for K a numberfield.}

    K := BaseRing(alg);

    require IsInvolutive(alg) :
        "Noninvolutive Algebra has no associated SU.";
    require K eq InvolutiveBaseRing(alg) :
        "The Algebra needs to be involutive over its BaseRing.";
    require ISA(Type(K), FldNum) or ISA(Type(K), FldRat) :
        "LocalRankOfSU is only implemented for number fields.";
    require alg eq Generic(alg) :
        "Can only get the local ranks in M_n(D) (this is the explicit isomorphism problem).";

    f1_in_alg := alg ! NumberField(place).1;
    require f1_in_alg eq _Conjugate(f1_in_alg) :
        "The place needs to be over a field fixed by the involution.";

    // the trivial case
    if Dimension(alg) eq 0 then
        return 0;
    end if;

    phi := GetFormOfInvolution(alg);

    return local_witt_index_single_place_in_F(phi, place);
end intrinsic;

/// If phi is defined over a numberfield, redefine that numberfield as absolute
/// over QNF() and redefine the entire algebra in this way
function _redefine_algebra_if_required(alg, phi)
    K := BaseRing(Parent(phi));
    if Type(K) eq FldRat then
        Q := QNF();
        assert IsInvolutive(K);
        Q := InvolutiveRing(Q ! 1);
        phi := Matrix(Q, phi);
        M := Parent(phi);
        M := InvolutiveAlgebra(M, map<M -> M | x :-> M ! _Conjugate(alg ! x)>);
        return phi, Q;
    end if;

    Q := QNF();
    _ := IsSubfield(Q, K);
    F, BR_to_F := relative_field_but_does_not_segfault(Q, K);
    assert IsInvolutive(K);
    F := InvolutiveRing(F, map<F -> F | x :-> BR_to_F(_Conjugate(Inverse(BR_to_F)(x)))>);
    phi := Matrix(F, phi);
    M := Parent(phi);
    M := InvolutiveAlgebra(M, map<M -> M | x :-> M ! _Conjugate(alg ! x)>);
    return phi, Q;
end function;

intrinsic LocalRankOfSU(alg::AlgMat, place::RngIntElt) -> RngIntElt
    {Trivial Overload where BaseRing(alg) is Q and the place a finite prime.}

    K := BaseRing(alg);
    require IsInvolutive(alg) :
        "Noninvolutive Algebra has no associated SU.";
    require K eq InvolutiveBaseRing(alg) :
        "The Algebra needs to be involutive over its BaseRing.";
    require ISA(Type(K), FldNum) or ISA(Type(K), FldRat) :
        "LocalRankOfSU is only implemented for number fields.";
    require alg eq Generic(alg) :
        "Can only get the local ranks in M_n(D) (this is the explicit isomorphism problem).";
    require IsPrime(place) :
        "When the place is a finite integer, it must be prime.";

    // the trivial case
    if Dimension(alg) eq 0 then
        return 0;
    end if;

    phi := GetFormOfInvolution(alg);

    // redefine phi over QNF(), and pull the place up
    phi, Q := _redefine_algebra_if_required(alg, phi);
    place := Decomposition(Q, place)[1][1];

    return local_witt_index_single_place_in_F(phi, place);
end intrinsic;

intrinsic LocalRankOfSU(alg::AlgMat, place::Infty) -> RngIntElt
    {Trivial Overload where BaseRing(alg) is Q and the place is infinity.}

    K := BaseRing(alg);
    require IsInvolutive(alg) :
        "Noninvolutive Algebra has no associated SU.";
    require K eq InvolutiveBaseRing(alg) :
        "The Algebra needs to be involutive over its BaseRing.";
    require alg eq Generic(alg) :
        "Can only get the local ranks in M_n(D) (this is the explicit isomorphism problem).";

    // the trivial case
    if Dimension(alg) eq 0 then
        return 0;
    end if;

    phi := GetFormOfInvolution(alg);

    // redefine phi over a field defined over QNF() and pull the place up
    phi, Q := _redefine_algebra_if_required(alg, phi);
    place := InfinitePlaces(Q)[1];

    return local_witt_index_single_place_in_F(phi, place);
end intrinsic;

intrinsic IsInvolutivelyClosed(sub::AlgMat, full::AlgMat) -> BoolElt
    {Check if sub is involutively closed wrt the involution of full.}
    require IsInvolutive(full) : "The full algebra is not involutive.";

    return forall{x : x in Basis(sub) | _Conjugate(full ! x) in sub};
end intrinsic;
