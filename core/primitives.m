////////////////
// Miscellaneous Functions
function get_maximal_idempotent(algebra)
    // find an element in algebra which is the multiplicative identity

    if Dimension(algebra) eq 0 then
        return false;
    end if;

    try
        idpot := algebra ! 1;
        return idpot;
    catch e
        ;
    end try;

    dec, idpots := DirectSumDecomposition(algebra);
    idpot := &+idpots;
    return algebra ! idpot;
end function;

function multiplication_but_works(scalar, matrix)
    // Yes. Yes, I have to redefine f***ing
    // multiplication of a matrix by a scalar
    // There are to many multiplications available
    // and for some matrices (e.g. over quaternions)
    // magma gets confused

    assert Parent(scalar) eq BaseRing(Parent(matrix));
    res := Matrix([[scalar * matrix[i][j]
                    : j in [1..NumberOfColumns(matrix)]]
                   : i in [1..NumberOfRows(matrix)]]);
    return Parent(matrix) ! res;
end function;

function coordinates_in_basis(x, basis)
    // Give the coordinates of the matrix x relative to basis
    //
    // INPUTS
    //  AlgMatElt x
    //  SeqEnum[Element of Parent(x)] basis
    // OUTPUTS
    //  SeqEnum[Coordinates of x relative to basis]
    // ASSUMPTIONS
    //  basis needs not be a basis of Parent(x), only be a linearly independent
    //      set of matrices with x \in span_F(basis) where F := BaseRing(Parent(x))

    assert ISA(Type(x), AlgMatElt);
    assert forall{b : b in basis | ISA(Type(b), AlgMatElt)};
    assert forall{b : b in basis | IsCoercible(Parent(x), b)};

    M := Parent(x);
    dim := Dimension(M);
    B := Basis(M);
    F := BaseRing(M);

    mat_space := RMatrixSpace(F, #basis, dim);
    basis_matrix := mat_space ! &cat[Coordinates(M, b) : b in basis];

    F_to_dim := RModule(F, dim);
    // the right hand side of the system of linear equations to solve
    // This is what we want but Magma somehow does not allow this????? idfk anymore
    // rhs := F_to_dim ! Coordinates(M, x);
    rhs := F_to_dim ! 0;
    for i in [1..dim] do
        bvect := F_to_dim ! [(j eq i) select 1 else 0
                                             : j in [1..dim]];
        rhs +:= Coordinates(M, x)[i] * bvect;
    end for;

    sol := Eltseq(Solution(basis_matrix, rhs));
    assert forall{i : i in [1..#basis] | Parent(sol[i]) eq BaseRing(M)};

    if GetAssertions() ge 3 then
        idpot := get_maximal_idempotent(M);
        assert Parent(idpot) eq M;
        assert &+[multiplication_but_works(sol[i], idpot) * basis[i] : i in [1..#basis]] eq x;
    end if;

    return sol;
end function;

function coordinates_in_basis_fld(x, basis)
    // Give the coordinates of the numberfieldelement x relative to `basis'
    //
    // INPUTS
    //  FldNumElt x
    //  List[Element of Parent(x)] basis
    // OUTPUTS
    //  List[Coordinates of x relative to basis]
    // ASSUMPTIONS
    //  basis needs not be a basis of Parent(x), only be a linearly independent set of elements with x \in span_K(basis)
    //      where K is the Field of Coefficients of Parent(x)
    // NOTES
    //  when Parent(x) is defined as an extension of K:
    //      Basis must be K-Basis of Parent(x) and the returned coordinates are elements of K relative to this K-Basis

    assert ISA(Type(x), FldNumElt);
    assert forall{b : b in basis | Parent(b) eq Parent(x)};

    M := Parent(x);
    B := Basis(M);
    K := BaseRing(M);
    basis_matrix := Matrix(K, [Eltseq(b, K) : b in basis]);
    sol := Solution(basis_matrix, Vector(K, Eltseq(x, K)));
    return Coordinates(VectorSpace(K, #basis),
                       sol);
end function;

function common_integral_basis(F)
    // Given a numberfield or FldRat F,
    // return an integral basis of F over its base field
    // and the base field

    if AbsoluteDegree(F) eq 1 then
        base_field := Rationals();
        basis_of_f := [base_field ! 1];
    else
        if not ISA(Type(F), FldNum) then
            F;
            error "F is not a number field";
        end if;
        base_field := BaseField(F);
        if AbsoluteDegree(base_field) eq 1 then
            base_field := Rationals();
        end if;
        // Dear future developer!
        // I have no Idea what the fuck is going on here.
        // You MUST call MaximalOrder(F) exactly twice
        // at this point, otherwise Magma will segfault
        // in some unrelated place way down the line.
        // Good Luck, Jonathan
        _ := MaximalOrder(F);
        basis_of_f := Basis(MaximalOrder(F), F);
        assert3 #basis_of_f eq Degree(F, base_field);
    end if;
    return basis_of_f, base_field;
end function;

function left_reg_with_integral_basis(gen)
    // For an element gen of F, calculate its left-regular representation via an integral basis
    //
    //  INPUTS
    //      FldNumElt gen in F
    //  OUTPUTS
    //      AlgMatElt representing gen, defined over BaseField(Parent(gen))

    F := Parent(gen);
    basis_of_f, base_field := common_integral_basis(F);

    basis_of_embedded_f := [];
    for b in basis_of_f do
        left_reg_coords := [coordinates_in_basis_fld(b * c, basis_of_f) : c in basis_of_f];
        Append(~basis_of_embedded_f, Transpose(Matrix(base_field, left_reg_coords)));
    end for;

    res := &+[coordinates_in_basis_fld(gen, basis_of_f)[i] * basis_of_embedded_f[i]
              : i in [1..Degree(F, base_field)]];

    assert2 MinimalPolynomial(res) eq MinimalPolynomial(gen);
    return res;
end function;

function find_smallest_prime_with_good_reduction_in_field(L)
    assert ISA(Type(L), FldNum);
    L_abs := AbsoluteField(L);

    p := 3;
    while true do
        assert3 IsPrime(p);
        if IsSquarefree(PolynomialRing(GF(p)) ! DefiningPolynomial(L_abs)) then
            return p;
        end if;
        p := NextPrime(p);
    end while;
end function;

function convert_local_ring_to_infinite_precision_approximation(upper_ring)
    // Convert a local ring to its infinite precision equivalent
    //
    // INPUTS
    //  RngPad upper_ring
    // OUTPUTS
    //  equivalent RngPad with infinite precision

    // R is a tower of two extensions, one unramified and one totally ramified
    // first get the two defining polynomials
    middle_ring := BaseRing(upper_ring);
    lower_ring := BaseRing(middle_ring);
    Zp := pAdicRing(Prime(upper_ring) : Exact);
    lower_def_poly := Polynomial([Integers() ! el :
                                  el in Eltseq(DefiningPolynomial(lower_ring))]);
    lower_as_exact := ext<Zp | lower_def_poly>;
    lower_to_lower_as_exact := map<
        lower_ring -> lower_as_exact |
        x :-> &+[(Integers() ! Eltseq(x)[i]) * lower_as_exact.1^(i-1)
                 : i in [1..Degree(lower_ring)]]>;
    middle_def_poly := Polynomial(
        [lower_to_lower_as_exact(el) : el in Eltseq(DefiningPolynomial(middle_ring))]);
    middle_as_exact := ext<lower_as_exact | middle_def_poly>;
    middle_to_middle_as_exact := map<
        middle_ring -> middle_as_exact |
        x :-> &+[(Integers() ! Eltseq(x)[i]) * middle_as_exact.1^(i-1)
                 : i in [1..Degree(middle_ring)]]>;

    upper_def_poly := Polynomial(
        [middle_to_middle_as_exact(el) : el in Eltseq(DefiningPolynomial(upper_ring))]);
    upper_as_exact := ext<middle_as_exact | upper_def_poly>;
    return InfinitePrecisionApproximation(upper_as_exact);
end function;

function cast_from_FldPad_to_RngLocA(R : MinPrecision:=100)
    // Convert R from RngPad to RngLocA
    //
    // INPUTS
    //  RngPad R
    //  RngIntElt MinPrecision:=100 : the precision to use if R has infinite precision
    // OUTPUTS
    //  <RngLogA that is isomorphic to R as a field,
    //   map from R to the RngLocA calculated>

    if not ISA(Type(R), RngPad) then
        error "Can only Cast RngPad.";
    end if;

    // there are no infinite precision versions of RngLocA
    if Precision(R) eq Infinity() then
        R := ChangePrecision(R, MinPrecision);
    end if;

    if AbsoluteDegree(R) eq 1 then
        res := LocalField(pAdicField(Prime(R), Maximum(Precision(R), MinPrecision)),
                                     Polynomial([-1,1]));
        map := map<R -> res |
            r :-> res ! r,
            x :-> R ! RepresentationMatrix(x)[1][1]>;
        assert3 Type(res) eq RngLocA;
        assert3 Precision(res) ge Precision(R);
        return res, map;
    end if;

    // the ring over which R is immediately defined
    base_ring := BaseRing(R);
    def_poly := DefiningPolynomial(R);
    base_res, base_map := cast_from_FldPad_to_RngLocA(
        base_ring : MinPrecision:=MinPrecision);
    // cast def_poly into base_res and get the extension
    res := LocalField(base_res, Polynomial([base_map(el) : el in Eltseq(def_poly)]));
    map := map<R -> res |
        r :-> &+[base_map(Eltseq(r)[j]) * res.1^(j-1): j in [1..Degree(res)]],
        // The weird RepresentationMatrix(y)[1] is just Eltseq(y),
        // but containing higher powers, even when the coefficients are 0
        x :-> &+[Inverse(base_map)(RepresentationMatrix(x)[1][j]) * R.1^(j-1): j in [1..Degree(res)]]>;

    assert3 Type(res) eq RngLocA;
    assert3 Precision(res) ge Precision(R);
    return res, map;
end function;

function relative_field_but_does_not_segfault(K, L)
    // RelativeField, but does not crash when AbsoluteDegree(K) eq AbsoluteDegree(L)

    if AbsoluteDegree(K) eq AbsoluteDegree(L) then
        res := ext<K | Polynomial([-1,1]) : DoLinearExtension:=true>;
        assert BaseRing(res) eq K;
        return res, map<L -> res | x :-> res ! x, y :-> L ! y>;
    end if;

    if not IsSubfield(K, L) then
        error "K is not a subfield of L";
    end if;
    res := RelativeField(K, L);

    is_iso, cast := IsIsomorphic(L, res);
    assert is_iso;

    assert BaseRing(res) eq K;
    return res, cast;
end function;

function find_isomorphism_type(algebra)
    // Calculate the field to which algebra is isomorphic
    //
    // ASSUMPTIONS
    //  algebra must be a matrix algebra defined over a field F
    //          isomorphic to a finite separable extension K|F
    //  This algorithm may(but is not guaranteed to) fail with an error when K|F is not separable
    //  BaseRing(algebra) must be a field which allows for extensions by arbitrary
    //      irreducible polynomials using ext<BaseRing(algebra) | f>
    // INPUTS
    //  AlgMat algebra
    // OUTPUTS
    //  Fld field that the algebra is isomorphic to
    //  Map[AlgMat, Fld] : isomorphism from the algebra into the field (invertible)

    F := BaseRing(algebra);
    if not ISA(Type(F), Fld) then
        error "The algebra must be defined over a field.";
    end if;

    if Dimension(algebra) eq 1 then
        return F, map<algebra -> F | x :-> coordinates_in_basis(x, Basis(algebra)), y :-> algebra.1 * y>;
    end if;

    // problem when algebra's 1 is not the identity matrix
    // need to calculate the maximal central idempotent
    dec, idpots := DirectSumDecomposition(algebra);
    if not #dec eq 1 then
        error "The algebra is not simple";
    end if;
    idpot := idpots[1];

    // first find the generator as an element of algebra
    over_degree := Degree(algebra);
    generator := Basis(algebra)[1];
    for b in [2..#Basis(algebra)] do
        c := 0;
        while true do
            c +:= 1;
            if c ge #Basis(algebra) + 1 then
                // in this case, the Algebra must be isomorphic to an inseparable extension
                // and we have no guarantee that the algorithm will work at all
                error "Extension is inseparable, find_isomorphism_type can not find a solution.";
            end if;

            generated_by_gen_and_cb := sub<
                algebra |
                generator + c * Basis(algebra)[b]>;
            if generator in generated_by_gen_and_cb and Basis(algebra)[b] in generated_by_gen_and_cb then
                generator +:= c * Basis(algebra)[b];
                break;
            end if;
        end while;
    end for;

    assert generator in algebra;

    // we have found the correct generator
    // get the nontrivial part of its minimal polynomial
    g := MinimalPolynomial(generator);
    for f in Factorization(g) do
        if Degree(f[1]) gt 1 then
            // f[1] is the minimal polynomial giving us the generator of K|F.
            K := ext<F | f[1]>;
            // Magma is weird. OptimizedRepresentation does not work for
            // numberfields which are not absolute.
            if ISA(Type(K), FldNum) and Type(BaseField(K)) eq FldRat then
                K_opt, K_to_K_opt := OptimizedRepresentation(K);
            else
                K_opt := K;
                K_to_K_opt := map<K -> K_opt | x :-> K_opt ! x>;
            end if;
            algebra_to_K := map<algebra -> K_opt |
                                x :-> &+[coordinates_in_basis(x,
                                                              [idpot * generator^(j-1) * idpot
                                                               : j in [1..Degree(K)]])[i]
                                          * K_to_K_opt(K.1)^(i-1)
                                         : i in [1..Degree(K)]],
                                y :-> &+[Eltseq(K ! y)[i] * idpot * generator^(i-1) * idpot
                                         : i in [1..Degree(K)]]>;
            return K_opt, algebra_to_K;
        end if;
    end for;
    error "Internal Error: could find a generator but no minimal polynomial factor in find_isomorphism_type";
end function;

function extends_finite(P, p)
    // GIVEN
    //  - two places
    // WHERE
    //  - P and p are finite
    //  - BaseField(NumberField(P)) eq NumberField(p)
    // CALCULATE
    //  - Whether P extends p (BoolElt)

    I := Ideal(P);
    i := Ideal(p);
    M := MaximalOrder(NumberField(P));
    i_top := ideal<M |i>;
    return i_top subset I;
end function;

function absolutize_place(F, place)
    // GIVEN
    //  - FldNum F
    //  - a place over F
    // CALCULATE
    //  - The AbsoluteField(F)
    //  - the cast F -> AbsoluteField(F)
    //  - a place of AbsoluteField(F) equivalent to place

    assert ISA(Type(F), FldNum);
    assert ISA(Type(place), PlcNumElt);
    assert F eq NumberField(place);

    if IsAbsoluteField(F) then
        return F, map<F -> F | x :-> x>, place;
    end if;

    F_abs := AbsoluteField(F);
    cast := map<F -> F_abs | x :-> F_abs ! x>;

    if IsFinite(place) then
        // this case is easy, we can push the generators of the Ideal into F_abs
        I := Ideal(place);
        I_abs := ideal<MaximalOrder(F_abs) | [cast(b) : b in Generators(I)]>;
        place_abs := Place(I_abs);
        return F_abs, cast, place_abs;
    else
        // this case is more difficult
        emb := [Evaluate(b, place) : b in Basis(F)];
        for P in InfinitePlaces(F_abs) do
            emb_abs := [Evaluate(cast(b), P) : b in Basis(F)];
            if emb eq emb_abs then
                return F_abs, cast, P;
            end if;
        end for;
        F;
        place;
        F_abs;
        error "Could not determine the image of an infinite valuation in the absolute field.";
    end if;
end function;


function extends_but_works(P, p)
    assert Type(P) eq PlcNumElt;
    assert Type(p) eq PlcNumElt;
    if IsFinite(P) then
        if not IsFinite(p) then
            P; p; error "Both places need to be Finite or Infinite";
        end if;
        return extends_finite(P, p);
    end if;

    if not IsInfinite(p) then
        P; p; error "Both places need to be Finite or Infinite";
    end if;

    // only the finite case seems to be buggy
    return Extends(P, p);
end function;

/// a version of Decomposition that has fewer wrong edge cases
function decomposition_but_works(F, p)
    assert ISA(Type(F), FldNum);
    // PlcNumElt
    if ISA(Type(p), PlcNumElt) then
        // Trivial Case, no decomposition to calculate
        if NumberField(p) eq F then
            return [<p, 1>];
        end if;

        // The prime is finite
        if IsFinite(p) then
            prime := Characteristic(ResidueClassField(p));

            // irrelevant BS start
            // NB: We just want Decomposition(F, prime), but that sometimes bugs out.
            // the following is a workaround.
            // Please do not ask me how this works,
            // I am not paid enough for this language.
            // NB2: yes, this next line is literally required. I have no Idea, why or what this is doing.
            // When F is the threefold trivial extension of Q by x - 1 and we don't redefine F
            // with the next line, OptimizedRepresentation sometimes fails for no discernable reason.
            why_is_this_necessary := ext<
                BaseField(F) |
                Polynomial(BaseField(F), Eltseq(DefiningPolynomial(F)))>;
            some_dumb_field_we_should_not_need := AbsoluteField(why_is_this_necessary);
            why_magma := OptimizedRepresentation(some_dumb_field_we_should_not_need);
            _ := Decomposition(why_magma, prime);
            // irrelevant BS end; this entire block is only used for undocumented sideeffects

            decomp_of_raw_prime := Decomposition(F, prime);
            res := [el : el in decomp_of_raw_prime | extends_but_works(el[1], p)];
            assert #res ge 1;
            return res;
        end if;

        // the prime is infinite - this is the only option left
        assert IsInfinite(p);
        assert NumberField(p) eq BaseField(F);
        return Decomposition(F, p);
    end if;

    if ISA(Type(p), RngIntElt) then
        assert IsPrime(p);
        return Decomposition(F, p);
    end if;

    is_integer, prime := IsCoercible(Integers(), p);
    if is_integer then
        assert IsPrime(prime);
        return Decomposition(F, prime);
    end if;

    if p cmpeq Infinity() then
        if IsAbsoluteField(F) then
            return Decomposition(F, Infinity());
        else
            decomp_to_bf := decomposition_but_works(BaseField(F), Infinity());
            decomp_to_F := [];
            for dec in decomp_to_bf do
                single_decomp_to_F := decomposition_but_works(F, dec[1]);
                decomp_to_F cat:= [<el[1], el[2] * dec[2]> : el in single_decomp_to_F];
            end for;
            for tup in decomp_to_F do
                assert3 Type(tup[1]) eq PlcNumElt and NumberField(tup[1]) eq F;
            end for;
            return decomp_to_F;
        end if;
    end if;

    F;
    Type(F);
    p;
    Type(p);
    "This place cannot be hit. Wrong input types?";
    assert false;
end function;

/// Like Decomposition(PlcNumElt), but works for relative extensions
function decomposition_group_but_works(place)
    L := NumberField(place);
    K := BaseRing(L);
    if K eq Rationals() then
        assert IsNormal(L);
        return Decomposition(place);
    end if;

    // calculate the decomposition group in L_abs
    Labs, L_to_Labs, place_in_L_abs := absolutize_place(L, place);
    absolute_aut_group, _, abstract_to_aut := AutomorphismGroup(Labs);
    absolute_decomp_group := DecompositionGroup(place_in_L_abs);

    // find K as a subfield of Labs by finding a root of K in Labs
    r := L_to_Labs(L ! K.1);
    // now get the subgroup of absolute_decomp_group that fixes r
    gens_fixing_k := [];
    for g in Generators(absolute_decomp_group) do
        if abstract_to_aut(g)(r) eq r then
            Append(~gens_fixing_k, g);
        end if;
    end for;
    decomp_group_on_absolute_roots := sub<absolute_aut_group | gens_fixing_k>;
    return decomp_group_on_absolute_roots;
end function;

/// GIVEN
///     x in a numberfield L | K
///     iobfg the image of K.1 under an involution of K
/// CALCULATE
///     the involution of K applied to all coordinates of x
function _apply_base_involution(x, iobfg)
    return &+[
            &+[Eltseq(Eltseq(x)[i])[j] * iobfg^(j-1)
                : j in [1..Degree(BaseField(Parent(x)))]
            ] * Parent(x).1^(i-1)
            : i in [1..Degree(Parent(x))]
        ];
end function;

/// GIVEN
///     An FldNum L
///     An element of L, image_of_L1
///     Option<An element of BaseField(L)>, iobfg
/// CALCULATE
///     The subfield of L fixed by the involution defined by
///     L.1 -> image_of_L1; BaseField(L).1 -> iobfg; linear on BaseField(BaseField(L))
///     Return type is FldNum
function calculate_fixed_field_raw(L, image_of_L1 : iobfg:=BaseField(L).1)
    if not IsAbsoluteField(L) then
        L_abs := AbsoluteField(L);
        image_abs := L_abs ! &+[_apply_base_involution(Eltseq(L ! L_abs.1)[i], iobfg)
            * image_of_L1^(i-1)
        : i in [1..Degree(L)]];
        ff_abs := calculate_fixed_field_raw(L_abs, image_abs);
        is_sub := IsSubfield(ff_abs, L);
        assert is_sub;
        assert ISA(Type(ff_abs), FldNum);
        return ff_abs;
    end if;

    // Given an absolute FldNum L and a primitive Element image_of_L1
    // calculate the fixed field in L under the aut moving L.1 -> image_of_L1

    if not Evaluate(DefiningPolynomial(L), image_of_L1) eq 0 then
        L;
        image_of_L1;
        Parent(image_of_L1);
        iobfg;
        MinimalPolynomial(image_of_L1);
        DefiningPolynomial(L);
        "image_of_L1 can not be the image of L.1";
        assert false;
    end if;

    if AbsoluteDegree(L) eq 1 then
        assert ISA(Type(L), FldNum);
        return L;
    end if;

    // find the involution as an element of Aut(L|Q)
    auts_L_Q := Automorphisms(L);
    for a in auts_L_Q do
        if not a(L.1) eq image_of_L1 then
            continue a;
        end if;
        F := FixedField(L, [a]);
        // this is the correct aut.
        assert Integers() ! (AbsoluteDegree(L) / AbsoluteDegree(F)) in {1, 2};
        if Type(F) eq FldRat then
            F := QNF();
            _ := IsSubfield(F, L);
        end if;
        assert ISA(Type(F), FldNum);
        return F;
    end for;
end function;

function direct_sum_decomposition_but_works(alg)
    if Type(alg) eq AlgMat and Dimension(alg) eq 0 then
        return [], [];
    end if;

    return DirectSumDecomposition(alg);
end function;

function is_isomorphic_fldnum_but_safer(K, F)
    return DefiningPolynomial(AbsoluteField(K)) eq DefiningPolynomial(AbsoluteField(F));
end function;

function fix_but_works(M)
    // Fix(ModGrp) does not always work for reducible modules

    assert ISA(Type(M), ModGrp);

    dec := DirectSumDecomposition(M);
    fixed_irreds := [el : el in dec | Fix(el) eq el];
    if #fixed_irreds eq 0 then
        return sub<M | 0>;
    end if;
    return &+fixed_irreds;
end function;

/// Return the irreducible module corresponding to irred_torus
///
/// Rationale:
///     the irreds are calculated at different places and therefore
///     are defined over incomparable groups
///     however, their basis elements form right-transversals over groups we know
///     so we can compare them to check whether they correspon
///     (i.e. are isomorphic modulo an additional isomorphism of their groups)
/// INPUTS
///  ModGrp irred_to_find: the irred to find in the list `irreds`
///  CharCollDAt first_collateral_data: the collateral data from the calculation of irred_to_find
///  SeqEnum[ModGrp] irreds: the irreducibles from a run of ranks_of_irreds at a different place
///  CharCollDat second_collateral_data: the collateral data from the calculation of irreds
/// OUTPUTS
///  BoolElt: a corresponding irred was found
///  RngIntElt: the index of the first irred in irreds corresponding to irred_torus. 0 if the first return is false
function corresponding_irred(
        irred_to_find, first_collateral_data,
        irreds, second_collateral_data)
    // Gal(EFhat | BF) for the run calculating irreds
    second_galois_group := second_collateral_data`galoisGroupOverBaseField;
    // X_EF ->> X_S for the run calculating irreds
    second_quotient_hom := second_collateral_data`characterQuotientHom;
    // Gal(EFhat | EF) for the run calculating irreds
    second_galois_to_extension_field := second_collateral_data`galoisGroupOverExtensionField;

    // G_complete, H_complete are the full galois groups from the two runs of ranks_of_irreds
    G_complete := first_collateral_data`galoisGroupOverBaseField;
    H_complete := second_galois_group;
    is_iso, g_to_h := IsIsomorphic(G_complete, H_complete);
    if not is_iso then return false; end if;

    // G and H are the descended action groups (i.e. quotients of *_complete)
    G := Group(Codomain(first_collateral_data`characterQuotientHom));
    H := Group(Domain(second_quotient_hom));

    // construct a matrix moving from Codomain(first_collateral_data`characterQuotientHom) to the
    // module of which irreds are quotients
    rows := [];
    for coset_rep_in_g in GSet(G) do
        // G acts naturally on first_collateral_data`galoisGroupOverBaseField, so the GSet elements are part of that group
        assert Parent(coset_rep_in_g) eq G_complete;
        our_coset := second_galois_to_extension_field * g_to_h(coset_rep_in_g);
        for pos in [1..#GSet(H)] do
            if our_coset eq second_galois_to_extension_field * GSet(H)[pos] then
                Append(~rows, [idx eq pos select 1 else 0 : idx in [1..#GSet(H)]]);
                break pos;
            end if;
        end for;
    end for;
    // the matrix, whose right-multiplication moves from X_EF used to calculate irred_to_find
    // to the corresponding X_EF used to calculate irreds
    first_XEF_to_second_XEF := Matrix(Rationals(), rows);
    // moving the basis elements of irred_to_find (a submodule of the first X_S)
    //  - first to the first X_EF [with Inverse(first_collateral_data`characterQuotientHom)]
    //  - then to the second X_EF [with first_XEF_to_second_XEF + the Eltseq and ! into Domain(second_quotient_hom)]
    //  - then to the second X_S [with second_quotient_hom]
    images := [second_quotient_hom(
        Domain(second_quotient_hom) !
            Eltseq(Inverse(first_collateral_data`characterQuotientHom)(x) * first_XEF_to_second_XEF))
               : x in Basis(irred_to_find)];
    // the images as a submodule of second X_S
    image_module, _ := sub<Codomain(second_quotient_hom) | images>;

    // now find the irreducible that is equal to this
    for irr_ind in [1..#irreds] do
        if irreds[irr_ind] eq image_module then
            return true, irr_ind;
        end if;
    end for;
    return false, 0;
end function;

