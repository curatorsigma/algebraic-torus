// General Overloads of Magma intrinsics

// this function is shitty, because it assumes that ulong on the machine
// is at most 64 bits long. I actually want concatenation of the literal
// bits instead of this roundabout addition.
// However, normal 64/32 bit architectures will usually have ulong = 32 or 64
// bits, in which case this is Hash(concatenation(Hash(y), Hash(curr))).
// (Note that Hash(x) = x for ints smaller then the max ulong.)
intrinsic Hash(x::List) -> RngIntElt
    {Hash the contents of the list.}
    curr := 0;
    for y in x do
        curr := Hash(Hash(y) + curr * 2^64);
    end for;
    return curr;
end intrinsic;

intrinsic IsDivisionRing(a::AlgQuat) -> BoolElt
    {Quaternion algebras are division rings when defined over division rings.}
    try
        res := IsDivisionRing(BaseRing(a));
        return res;
    catch e
        return false;
    end try;
end intrinsic;




// Some quality-of-life functions for RngLocA
intrinsic AbsoluteDegree(F::RngLocA) -> RngIntElt
    {The Absolute Degree of F. Was that so hard, Magma?}
    return Degree(F) * AbsoluteDegree(BaseRing(F));
end intrinsic;

intrinsic BaseField(F::RngLocA) -> Rng
    {BaseRing(F) always returns a Fld, but BaseField is not defined?!?!?!?}
    return BaseRing(F);
end intrinsic;

intrinsic AbsoluteBaseField(F::RngLocA) -> FldPad
    {The Absolute Base (i.e. the termination of BaseRing^*(F))}
    if ISA(Type(BaseRing(F)), FldPad) then
        return BaseRing(F);
    else
        return AbsoluteBaseField(BaseRing(F));
    end if;
end intrinsic;




// helpers for AbsoluteField(RngLocA) -> RngLocA

/// Give the coordinates of the RngLocAElt x relative to basis
///
/// INPUTS
///  RngLocAElt x
///  SeqEnum[RngLocAElt] basis : a set of elements in Parent(x), containing x in their spanning set
///  RngLocA or FldPad base_field=BaseRing(Parent(x)):
///      the spanning set is to be taken over this field
/// OUTPUTS
///  List[Coordinates of x relative to basis]
/// ASSUMPTIONS
///  basis is linearly independent over base_field
/// NOTES
///  We only assert, but can not guarantee that the result lies in base_field
function coords_to_basis(x, basis : base_field:=BaseRing(Parent(x)))

    assert ISA(Type(x), RngLocAElt);

    M := Parent(x);
    basis_matrix := Transpose(Matrix(M, [basis]));
    sol, ker := Solution(basis_matrix, Vector(M, [x]));
    sol := Eltseq(sol);
    assert forall{y : y in sol | y in base_field};
    return [base_field ! el : el in sol];
end function;

/// Return true iff f is squarefree in var
function is_squarefree(f, var)
    return Degree(GreatestCommonDivisor(f, Derivative(f, var))) eq 0;
end function;

/// Given a square free polynomial f over k(a), defined by the MinPol P_a
///
/// Calculate
///  - an integer s
/// Define
///  - g(x, a) := f(x - sa, a)
/// Return Norm_{k(a) | k}(g) in k[X]
/// The output is square free over k[X].
function sqfr_norm(f, P_a)

    ka := CoefficientRing(Parent(f));
    a := ka.1;
    k := CoefficientRing(Parent(P_a));
    // z1 is the first entry of g
    // z2 is the second entry of g
    R<z1, z2> := PolynomialRing(ka, 2);
    P_a_multivar := &+[z2^j * Eltseq(P_a)[j + 1] : j in [0..Degree(P_a)]];

    // initialize
    s := 0;
    while true do
        // g(x, a) = f(x - sa, a)
        // we want the resultant RES_y(P_a(y), g(x, y))
        // first create g(x, y) in k[z1, z2]
        // first-first, create g(x, a) in k(a)[z1]
        g_in_ka := R ! 0;
        for i in [0..Degree(f)] do
            // f is represented as a polynomial in k(a)[X].
            // This is the coefficient in front of X^i
            coeff := Eltseq(f)[i + 1];
            g_in_ka +:= coeff * (z1 - s * a)^i;
        end for;
        // we now have a polynomial in k(a)[z1],
        // and we instead need it with a -> z2
        g := R ! 0;
        for i in [1..Degree(g_in_ka, z1)+1] do
            // this is g_in_ka decomposed relative to z1
            coeff := Coefficients(g_in_ka, z1)[i];
            // convert coeff from k(a) to k[z2]
            // since g_in_ka is in k(a)[z1], the coefficients should all be in k(a)
            assert TotalDegree(coeff) eq 0;
            tmp := Eltseq(TrailingCoefficient(coeff));
            g +:= &+[z2^(j - 1) * z1^(i-1) * tmp[j] : j in [1..#tmp]];
        end for;

        resultant := Resultant(P_a_multivar, g, z2);
        // Assert that the result is now in k[z1]
        assert2 Degree(resultant, z2) eq 0;
        assert2 forall{x : x in Coefficients(resultant, z1) | x in k};

        if is_squarefree(resultant, z1) then
            // convert resultant to a polynomial in k[X]
            S<X> := PolynomialRing(k);
            r_as_upol := &+[X^(j-1) * (k ! Coefficients(Coefficients(resultant, z1)[j])[1])
                            : j in [1..Degree(resultant, z1) + 1]];
            return s, g, r_as_upol;
        end if;
        s +:= 1;
    end while;
end function;

/// Given a local field F which is not defined over pAdicField,
/// return an isomorphic Field defined over BaseRing(BaseRing(F))
///
/// ALGORITHM
///  [Barry M. Trager. 
///   Algebraic factoring and rational function integration.
///   In R.D. Jenks, editor, Proc. SYMSAC '76, pages 196--208. ACM press, 1976.]
///      Their Algorithm 'primitive_element'
function _primitize_step(F)

    ka := BaseRing(F);
    f := DefiningPolynomial(F);
    k := BaseRing(ka);
    P_a := DefiningPolynomial(ka);

    s, g, primitive_poly := sqfr_norm(f, P_a);
    assert Degree(primitive_poly) eq Degree(F, k);
    new_field := LocalField(k, primitive_poly);

    // find the primitive elements of ka and F|ka in F
    // so we can decompose elements relative to this basis
    // first insert the primitive element into the first component of g
    T<y> := PolynomialRing(new_field);

    g_prim_y := T ! 0;
    for i in [1..Length(g)] do
        mon := Monomials(g)[i];
        coeff := Coefficients(g)[i];
        g_prim_y +:= (BaseRing(new_field) ! coeff) * y^(Degree(mon, 2)) * new_field.1^(Degree(mon, 1));
    end for;

    assert g_prim_y in T;
    assert Degree(g_prim_y) eq Degree(g, 2);
    // and move P_a into T
    P_a_in_T := &+[y^(k-1) * Eltseq(P_a)[k] : k in [1..Degree(P_a)+1]];

    common_divisor := GreatestCommonDivisor(g_prim_y, P_a_in_T);

    // TODO / NOTE: this may fail because GCD looses precision
    // I am unsure if there is a way to handle this safely or recover when this assert fails
    assert Degree(common_divisor) eq 1;
    // this is the generator of k(a) over k as an element in new_field
    a := - Eltseq(common_divisor)[1] / Eltseq(common_divisor)[2];
    // this is the generator of F over k(a) as an element in new_field
    b := new_field.1 - s * a;

    // get a root in F of the primitive polynomial
    root_in_F := Roots(primitive_poly, F)[1][1];
    assert3 root_in_F in F;

    // a cast from F to new_field
    cast_fwd := map<F -> new_field | x :->
        &+[b^(j-1) * a^(k-1) * Eltseq(Eltseq(x)[j])[k]
           : k in [1..#Eltseq(Eltseq(x)[j])],
             j in [1..#Eltseq(x)]]>;

    // a cast from new_field to F
    // recall that new_field.1 and root_in_F both satisfy primitive_poly
    cast_back := map<new_field -> F | x :-> 
        &+[Eltseq(x)[j] * root_in_F^(j-1) : j in [1..#Eltseq(x)]]>;
    cast := map<F -> new_field | x :-> cast_fwd(x), y :-> cast_back(y)>;

    return new_field, root_in_F, cast;
end function;

intrinsic AbsoluteField(F::RngLocA) -> RngLocA, Map[RngLocA, RngLocA]
    {Given a local Field F, return an isomorphic field defined over pAdicField.}

    curr := F;
    cast := map<F -> F | x :-> x>;
    primitive := F.1;
    while true do
        if AbsoluteDegree(BaseRing(curr)) eq 1 then
            break;
        end if;
        curr, primitive, cast := _primitize_step(curr);
    end while;

    assert AbsoluteDegree(curr) eq Degree(curr);

    // the absolute field
    return curr, cast;
end intrinsic;
