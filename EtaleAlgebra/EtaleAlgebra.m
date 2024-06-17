// The AlgEta Type and related functions
import "../core/primitives.m" :
    relative_field_but_does_not_segfault,
    find_isomorphism_type,
    left_reg_with_integral_basis,
    coordinates_in_basis_fld,
    coordinates_in_basis,
    is_isomorphic_fldnum_but_safer,
    common_integral_basis;

declare type AlgEta[AlgEtaElt];
declare attributes AlgEta :
    // the field over which this algebra is defined
    baseField,
    // a list of the extensions that make up this abstract etale algebra
    extensions,
    // All Constructors may redefine Numberfields. This gets
    // the exact fields which were specified when the algebra was constructed,
    // which allows us to do the coercion into the current fields so the user
    // does not have to
    originalFields,

    // OPTIONAL (existence must be checked)
    // for each field an element of an algebra representing field.1
    // all these elements must lie in the same algebra. then this etale algebra
    // embeds into the given algebra when all the realizing elements are consistent
    realizingElements,
    // ALWAYS SET WHEN realizingElements is set
    // this contains the primitive central idempotent (i.e. the identity element in the realization)
    // for each field
    centralIdempotents;

declare attributes AlgEtaElt :
    // the algebra this element belongs to
    Parent,
    // for each field, a number in that field defining the corresponding entry of the element
    entries;

/// Given x, find y such that:
///  The hom original.1 -> x is equivalent to our.1 -> y
/// up to coercion
/// INPUTS
///  FldNum original
///  FldNum our
///  AlgElt or FldNumElt with defined multiplication by elements of original: x
/// OUTPUTS
///  y
function image_of_original_to_image_of_our_raw(original, our, x)
    if x eq Parent(x) ! 0 then
        return Parent(x) ! 0;
    end if;

    if not Type(BaseField(original)) eq FldRat and Type(BaseField(our)) eq FldRat then
        assert2 IsSubfield(BaseField(original), BaseField(our));
    end if;
    assert AbsoluteDegree(our) eq AbsoluteDegree(original);
    assert2 is_isomorphic_fldnum_but_safer(our, original);

    // we now have the field towers
    // original | B
    // our | alg`baseField | ... | B
    // and original and our are isomorphic.
    y := &+[Eltseq(original ! our.1)[i] * x^(i-1) : i in [1..Degree(original)]];

    // move original.1 via the new map and assert the correct minimal polynomial
    if GetAssertions() ge 2 then
        image_of_original_1 := &+[Eltseq(our ! original.1)[i] * y^(i-1) : i in [1..Degree(our)]];
        assert2 Evaluate(MinimalPolynomial(x), image_of_original_1) eq 0;
    end if;

    return y;
end function;

/// Given x, find y such that:
///  The hom original.1 -> x is equivalent to our.1 -> y
/// up to coercion
/// INPUTS
///  AlgEta alg
///  FldNumElt or AlgMatElt or AlgEtaElt x
///  RngIntElt index : the index of the field in alg
/// OUTPUTS
///  y
function image_of_original_to_image_of_our(alg, x, index)
    our_field := alg`extensions[index];
    original_field := alg`originalFields[index];

    res := image_of_original_to_image_of_our_raw(original_field, our_field, x);
    assert Parent(res) eq Parent(x);
    return res;
end function;

/// Return the largest field which is a subfield of K and L
///
/// INPUTS
///  FldNum K
///  FldNum L
/// OUTPUTS
///  FldNum over Rationals() which IsSubfield(..., K) and IsSubfield(..., L)
///  and which is maximal with this property
function largest_common_subfield(K, L)
    assert ISA(Type(K), FldNum);
    assert ISA(Type(L), FldNum);

    K_lat := SubfieldLattice(K);
    assert Type(K_lat) eq SubFldLat;

    // traverse from Q upwards to K
    current_best := Bottom(K_lat);
    while true do
        assert Type(current_best) eq SubFldLatElt;
        superfields := MinimalOverfields(current_best);
        changed := false;
        for super in superfields do
            assert Type(super) eq SubFldLatElt;
            nflsup := NumberField(super);
            assert ISA(Type(nflsup), FldNum) or Type(nflsup) eq FldRat;
            if IsSubfield(nflsup, L) then
                current_best := super;
                changed := true;
                break;
            end if;
        end for;
        // we could not make a new step
        if not changed then
            break;
        end if;
    end while;
    assert3 Type(current_best) eq SubFldLatElt;
    res := NumberField(current_best);
    if Type(res) eq FldRat then
        res := QNF();
    end if;
    assert3 ISA(Type(res), FldNum);
    return res;
end function;

/// Check whether the (already set) realization is actually consistent
///
/// CHECKS
///  - isomorphism types are correct
///  - directness of the resulting realizing algebras
function realization_is_consistent(alg)
    if Dimension(alg) eq 0 then
        return true;
    end if;

    super_alg := Parent(alg`realizingElements[1]);
    realizing_summands := [sub<super_alg | alg`realizingElements[i]>
                           : i in [1..#alg`extensions]];
    // check pairwise disjointness of realizing summands
    for i in [1..#realizing_summands] do
        F, _, _ := find_isomorphism_type(realizing_summands[i]);
        if not IsIsomorphic(F, alg`extensions[i]) then
            return false;
        end if;
        for j in [i+1..#realizing_summands] do
            if not Dimension(realizing_summands[i] meet realizing_summands[j]) eq 0 then
                return false;
            end if;
        end for;
    end for;

    return true;
end function;

intrinsic EtaleAlgebra(list_of_extensions::[FldNum] : list_of_realizing_elements:=false) -> AlgEta
    {Create an etale algebra from the given list of fields.
    Use the largest basefield possible.

    list_of_realizing_elements, if given, must be a SeqEnum of elements of some matrix algebra
        each of which is the image of the generator of the corresponding field in an embedding
        into this algebra.}

    require #list_of_extensions gt 0 :
        "I cannot determine the GroundField from an empty list of extensions.";

    assert ISA(Type(list_of_extensions[1]), FldNum);

    // make one pass through the extensions to get the smallest field
    // by absolute degree and try to use that as basefield

    base_field_candidate := list_of_extensions[1];
    for field in list_of_extensions do
        if AbsoluteDegree(field) lt AbsoluteDegree(base_field_candidate) then
            base_field_candidate := field;
        end if;
    end for;
    base_field_candidate := AbsoluteField(base_field_candidate);

    // now make a second pass, potentially reducing the base field even further
    for field in list_of_extensions do
        base_field_candidate := largest_common_subfield(base_field_candidate, field);
    end for;

    return EtaleAlgebra(list_of_extensions, base_field_candidate
        : list_of_realizing_elements:=list_of_realizing_elements);
end intrinsic;

intrinsic EtaleAlgebra(list_of_extensions::[FldNum], base_field::FldNum
         : list_of_realizing_elements:=false,
           list_of_primitive_central_idempotents:=false) -> AlgEta
    {Create an etale algebra from the given list of fields and a given base_field.

    list_of_realizing_elements, if given, must be a SeqEnum of elements of some matrix algebra
        each of which is the image of the generator of the corresponding field in an embedding
        into this algebra.}

    if not list_of_realizing_elements cmpeq false then
        require Type(list_of_primitive_central_idempotents) eq SeqEnum :
            "list_of_realizing_elements cannot be given without primitive central idempotents as SeqEnum.";
        require Type(list_of_realizing_elements) eq SeqEnum :
            "if given, list_of_realizing_elements must be a SeqEnum";
        require #list_of_realizing_elements eq #list_of_extensions :
            "realizing elements are given, but not the correct number.";
        realizing_algebra := Parent(list_of_realizing_elements[1]);
        require forall{x : x in list_of_realizing_elements | Parent(x) eq realizing_algebra} :
            "realizing elements must all be in the same algebra.";
        require forall{x : x in list_of_primitive_central_idempotents
                       | Parent(x) eq realizing_algebra} :
            "primitive central idempotents must all live in the same algebra as the realizing elements.";
        require forall{i : i in [1..#list_of_extensions] | Evaluate(
                MinimalPolynomial(list_of_realizing_elements[i]),
                list_of_extensions[i].1) eq 0}:
            "The realizing elements satisfy the wrong minimal polynomials.";
    end if;

    // make one pass through the extensions and check the basefield
    for field in list_of_extensions do
        require IsSubfield(base_field, field) :
            "At least one of the fields is not an extension of base_field";
    end for;

    etale_algebra := New(AlgEta);
    etale_algebra`baseField := base_field;
    etale_algebra`originalFields := list_of_extensions;

    if not list_of_realizing_elements cmpeq false then
        etale_algebra`realizingElements := list_of_realizing_elements;
        etale_algebra`centralIdempotents := list_of_primitive_central_idempotents;
    end if;

    etale_algebra`extensions := [];
    // make a second pass and redefine all fields over the given base field
    for index in [1..#list_of_extensions] do
        // find the redefined field
        redefined_field := relative_field_but_does_not_segfault(
            etale_algebra`baseField,
            AbsoluteField(list_of_extensions[index]));
        Append(~etale_algebra`extensions, redefined_field);

        // redefine the realizing element if a realization is given
        if not list_of_realizing_elements cmpeq false then
            require IsSubfield(BaseField(etale_algebra`originalFields[index]),
                               etale_algebra`baseField) :
                "Each field must be defined over a field which is embeddable into the baseField for Realization to be computable.";
            etale_algebra`realizingElements[index] := image_of_original_to_image_of_our(
                etale_algebra, etale_algebra`realizingElements[index], index);
            assert3 Evaluate(MinimalPolynomial(etale_algebra`realizingElements[index]),
                             redefined_field.1) eq 0;
        end if;
    end for;

    return etale_algebra;
end intrinsic;

intrinsic EtaleAlgebra(list_of_extensions::[FldNum], base_field::FldRat
        : list_of_realizing_elements:=false,
          list_of_primitive_central_idempotents:=false) -> AlgEta
    {Create an etale algebra from the given list of fields and a given base_field.}

    Q := QNF();
    return EtaleAlgebra(list_of_extensions, Q
                        : list_of_realizing_elements:=list_of_realizing_elements,
                          list_of_primitive_central_idempotents:=list_of_primitive_central_idempotents);
end intrinsic;

intrinsic EtaleAlgebra(algebra::AlgMat) -> AlgEta, Map[AlgMat, AlgEta]
    {Create an etale algebra isomorphic to the given AlgMat.

    INPUTS
        AlgMat algebra: The Algebra to convert
    OUTPUTS
        AlgEta : the etale algebra AlgMat is isomorphic to
        Map[AlgMat, AlgEta] : an isomorphism between the two
        AlgEtaInv : if algebra is involutive, the corresponding involution on the etale algebra
    ASSUMES
        algebra must be etale
        algebra must be a subalgebra of an algebra in IsNormalFormCSA}

    // require normal form
    generic := Generic(algebra);
    n := Degree(generic);
    K := BaseRing(generic);

    if not (ISA(Type(K), FldNum) or Type(K) eq FldRat) then
        ExtendedType(K);
        error "The BaseRing must be FldNum or FldRat";
    end if;

    require Degree(K, PrimeField(K)) lt Infinity() :
        "The Algebra must be defined over a field which is a finite extension of its prime field.";

    require not Characteristic(K) eq 2 :
        "Algorithms for characteristic 2 are currently not implemented.";
    // convert the algebra into an AlgAss over a field.
    associative_super, gen_to_ass, ass_to_gen := AssociativeAlgebraOfNormalFormCSA(generic);
    alg_as_ass := sub<associative_super | [gen_to_ass(el) : el in Basis(algebra)]>;

    // Since algebra is guaranteed to be etale
    // DirectSumDecomposition(algebra) consists of fields
    // and we can find them with find_isomorphism_type
    decomp, idpots := DirectSumDecomposition(alg_as_ass);
    list_of_realizing_elements := [];
    list_of_primitive_central_idempotents := [];
    fields := [];
    for i in [1..#decomp] do
        el := decomp[i];
        field, alg_to_field := find_isomorphism_type(el);
        Append(~fields, field);
        Append(~list_of_realizing_elements, ass_to_gen(Inverse(alg_to_field)(field.1)));
        Append(~list_of_primitive_central_idempotents, ass_to_gen(idpots[i]));
    end for;

    res := EtaleAlgebra(fields, K :
        list_of_realizing_elements:=list_of_realizing_elements,
        list_of_primitive_central_idempotents:=list_of_primitive_central_idempotents);

    // the function from algebra into the resulting etale algebra is defined as follows
    // the powers of the realizing elements form a basis of algebra
    // and we decompose the element in algebra by this basis, writing the components
    // into the fields of the etale algebra (field.1^j <-> realizer^j)
    basis_in_algebra := [ElementRealization(res ! [
                            (k eq i) select res`extensions[i].1^(j-1) else 0
                                                   : k in [1..#res`extensions]])
                         : j in [1..Degree(res`extensions[i])],
                            i in [1..#res`extensions]];

    assert2 #basis_in_algebra eq Dimension(algebra);
    assert3 algebra eq sub<algebra | basis_in_algebra>;

    // the k-th basis vector in basis_in_algebra corresponds to indices i,j
    running_to_pair := [];
    i := 1;
    while i le #res`extensions do
        for j in [1..Degree(res`extensions[i])] do
            Append(~running_to_pair, <i, j>);
        end for;
        i +:= 1;
    end while;

    assert #running_to_pair eq Dimension(algebra);

    alg_to_eta := map<algebra -> res |
        x :-> &+[res ! [(running_to_pair[k][1] eq l)
                  select coordinates_in_basis(x, basis_in_algebra)[k]
                      * res`extensions[l].1^(running_to_pair[k][2] - 1)
                  else 0
                        : l in [1..#res`extensions]]
                 : k in [1..Dimension(algebra)]],
        y :-> ElementRealization(y)>;

    if GetAssertions() ge 3 then
        sa := sub<algebra | basis_in_algebra>;
        for b in Basis(algebra) do
            assert3 b in sa;
            in_res := alg_to_eta(b);
            assert3 Inverse(alg_to_eta)(in_res) eq b;
            assert3 Evaluate(MinimalPolynomial(b), in_res) eq res ! 0;
        end for;
    end if;


    // as the last step, convert the involution if possible
    if not IsInvolutive(algebra) then
        return res, alg_to_eta, false;
    end if;

    // calculate the image of K.1 as an element of K
    // (move it back to algebra, conjugate there, move it back and extract it as an element of K)
    iobfg := K ! Eltseq(alg_to_eta(_Conjugate(Inverse(alg_to_eta)(res ! K.1))))[1];

    // now calculate the images of each of the field generators in res
    iofgs := [];
    for i in [1..#res`extensions] do
        // first get the generator in the algebra
        field_1_in_res := res ! [(k eq i) select res`extensions[i].1 else 0
                                 : k in [1..#res`extensions]];

        // move it to the realization, conjugate, move back
        image_of_field_1 := alg_to_eta(_Conjugate(Inverse(alg_to_eta)(field_1_in_res)));
        // check that nothing went wrong here: Involutions leave the MinimalPolynomial invariant
        assert2 Evaluate(MinimalPolynomial(res`extensions[i].1) * Polynomial([0,1]),
              image_of_field_1) eq res ! 0;

        Append(~iofgs, image_of_field_1);
    end for;
    res := InvolutiveAlgebra(res, iofgs, iobfg);

    return res, alg_to_eta;
end intrinsic;

intrinsic DirectSum(A::AlgEta, B::AlgEta : strict_base_field:=true) -> AlgEta
    {Direct sum A + B.

    Auto-Reduce groundfield when possible and strict_base_field eq false.
    Create the realization as the direct sum, if both algebras have one set.
        In this case, they must both be AlgAss or AlgMat and the result is AlgMat.}

    if strict_base_field then
        require A`baseField eq B`baseField :
            "The basefields are not equal.";
        new_base_field := A`baseField;
    else
        new_base_field := largest_common_subfield(A`baseField, B`baseField);
    end if;

    // set realization only when both algebras have a realization set
    list_of_realizing_elements := false;
    if IsRealized(A) and IsRealized(B) then
        a_real := Parent(A`realizingElements[1]);
        b_real := Parent(B`realizingElements[1]);
        if Type(a_real) eq Type(b_real) then
            list_of_realizing_elements :=
                A`realizingElements cat B`realizingElements;
        end if;
        if Type(a_real) eq AlgAss and Type(b_real) eq AlgMat then
            a_real_as_mat := MatrixAlgebra(a_real);
            new_real := DirectSum(a_real_as_mat, b_real);
            list_of_realizing_elements :=
                [new_real ! el : el in A`realizingElements] cat
                [new_real ! el : el in B`realizingElements];
        end if;
        if Type(a_real) eq AlgMat and Type(b_real) eq AlgAss then
            b_real_as_mat := MatrixAlgebra(b_real);
            new_real := DirectSum(a_real, b_real_as_mat);
            list_of_realizing_elements :=
                [new_real ! el : el in A`realizingElements] cat
                [new_real ! el : el in B`realizingElements];
        end if;
    end if;

    return EtaleAlgebra(A`extensions cat B`extensions, new_base_field
                        : list_of_realizing_elements:=list_of_realizing_elements);
end intrinsic;

intrinsic DirectSum(algebras::[AlgEta] : strict_base_field:=true) -> AlgEta
    {Trivial Redirect to DirectSum(AlgEta, AlgEta : BoolElt).}

    require #algebras gt 0 :
        "I cannot determine the basefield of an empty direct sum of AlgEta's.";

    current_algebra := algebras[1];
    for i in [2..#algebras] do
        current_algebra := DirectSum(
            current_algebra, algebras[i] :
            strict_base_field:=strict_base_field);
    end for;
    return current_algebra;
end intrinsic;

intrinsic Dimension(algebra::AlgEta) -> RngIntElt
    {Dimension of algebra over its base Field.}
    if #algebra`extensions eq 0 then
        return 0;
    end if;

    return &+[Degree(field) : field in algebra`extensions];
end intrinsic;

intrinsic Print(algebra::AlgEta)
    {Print intrinsic for an etale algebra.}
    printf "EtaleAlgebra over the baseField %o of Dimension %o",
        algebra`baseField, Dimension(algebra);
end intrinsic;

intrinsic BaseField(algebra::AlgEta) -> FldNum
    {Get the baseField attribute.}
    return algebra`baseField;
end intrinsic;

intrinsic BaseRing(algebra::AlgEta) -> FldNum
    {Get the baseField attribute.}
    return algebra`baseField;
end intrinsic;

/// GIVEN
/// - a list of lists of ints
///
/// CALCULATE
/// - whether a solution exists and the solution if available:
/// - a list of ints of the same length as the list of lists
///     - at each index, the solution contains an element of the
///       input list at that index
///     - the solution contains each element at most once
///
/// INPUTS
///     list[list[int]] lists
///     list[int] selected: the first part of a potential solution
/// OUTPUTS
///     bool True iff a solution exists that starts with selected
///     list[int] a solution, starting with selected
/// NOTES
///     selected is used internally to track the state of a
///     recursive backtracking algorithm
function _choose_elements(lists : selected:=[])
    if #selected eq #lists then
        return true, selected;
    end if;

    for x in lists[#selected + 1] do
        // we may not choose an element that was already selected
        if x in selected then
            continue x;
        end if;

        // recurse into the right tail of the list, with x selected
        x_yields_solution, solution := _choose_elements(
            lists : selected:=Append(selected, x));
        if x_yields_solution then
            return true, solution;
        end if;
    end for;

    // no solution exists when the current state is `selected`
    return false, [];
end function;

intrinsic IsIsomorphicToSubAlgebra(A::AlgEta, B::AlgEta) -> BoolElt, Map[AlgEta, AlgEta], <>
    {Check whether A is isomorphic to a subalgebra of B.

    OUTPUTS
        BoolElt Is A isomorphic to a sub-algebra of B
        Map[AlgEta, AlgEta] embedding A -> B if possible
        Tuple<> Information used by IsIsomorphic to construct the inverse embedding if A == B

    Return the Answer as a Bool and an embedding of baseField-algebras
    A -> B when an embedding is possible}


    // if the basefields are not isomorphic, the algebras are not isomorphic
    if not IsIsomorphic(BaseField(A), BaseField(B)) then
        return false, 0, <0,0>;
    end if;

    // go over each extension E in A
    // - get all the extensions in B into which E embeds
    // Then take this information and calculate a complete embedding
    // - return false, 0 if none exists
    // - return true and the complete embedding if one exists

    possible_embeddings := [];
    embedding_j_to_map := [];
    for i in [1..#A`extensions] do
        Append(~possible_embeddings, []);
        Append(~embedding_j_to_map, AssociativeArray());
        for j in [1..#B`extensions] do
            is_sub, map := IsSubfield(A`extensions[i], B`extensions[j]);
            if not is_sub then
                continue j;
            end if;

            Append(~possible_embeddings[i], j);
            embedding_j_to_map[i][j] := map;
        end for;

        // short circuit if A`extensions[i] is not embeddable at all
        if #possible_embeddings[i] eq 0 then
            return false, 0, <0,0>;
        end if;
    end for;

    is_embeddable, embedding_indices := _choose_elements(possible_embeddings);
    if not is_embeddable then
        return false, 0, <0,0>;
    end if;

    // an embedding is possible. Now we need to calculate the map
    // that defines it
    // This map maps the elements in A[i] to the correct B[j] with the correct map
    // and extends this linearly to the whole of A.
    coercion := map<
        A -> B | x :-> &+[B ! [*(j eq embedding_indices[i])
                                    select embedding_j_to_map[i][j](Eltseq(x)[i])
                                    else B`extensions[j] ! 0
                               : j in [1..#B`extensions]*]
                          : i in [1..#A`extensions]]>;

    return true, coercion,
           <embedding_indices,
            [embedding_j_to_map[i][embedding_indices[i]] : i in [1..#A`extensions]]>;
end intrinsic;

intrinsic IsIsomorphic(A::AlgEta, B::AlgEta) -> BoolElt, Map[AlgEta, AlgEta]
    {Check whether two etale algebras are isomorphic.

    If possible, return an isomorphism of baseField-Algebras from A to B.}

    // if the basefields are not isomorphic, the algebras are not isomorphic
    if not IsIsomorphic(BaseField(A), BaseField(B)) then
        return false, 0;
    end if;

    // If A and B do not have the same number of fields, they
    // cannot be isomorphic
    //  (because K_1 + K_2 cannot embed into L for K_1, K_2, L fields)
    if #A`extensions ne #B`extensions then
        return false, 0;
    end if;

    a_sub_b, A_to_B, collateral_data := IsIsomorphicToSubAlgebra(A, B);

    if not a_sub_b then
        return false, 0;
    end if;

    // A is embeddable into B
    embedding_indices, embeddings := Explode(collateral_data);

    // If any field in A is embedded in a strictly larger field
    // (i.e. one that is not isomorphic), A and B cannot be isomorphic
    for i in [1..#embedding_indices] do
        if not IsIsomorphic(A`extensions[i], B`extensions[embedding_indices[i]]) then
            return false, 0;
        end if;
    end for;

    // each field of A was embedded into an isomorphic field
    // and A and B have the same number of fields

    // A and B are isomorphic.
    // we know that each used_coercion is an isomorphism of fields.
    // We have to use the reverse of embeddings to get the coercion B -> A
    back_summands := [0 : i in [1..#embedding_indices]];
    back_coercions := [*0 : i in [1..#embedding_indices]*];
    for i in [1..#embedding_indices] do
        back_summands[embedding_indices[i]] := i;
        back_coercions[embedding_indices[i]] := embeddings[i];
    end for;

    iso := map<A -> B | x :-> A_to_B(x),
                        y :-> &+[A ! [(j eq back_summands[i])
                                            select back_coercions[i](Eltseq(y)[i])
                                            else 0
                                         : j in [1..#back_summands]]
                                    : i in [1..#back_summands]]>;
    return true, iso;
end intrinsic;

intrinsic 'eq'(A::AlgEta, B::AlgEta) -> BoolElt
    {Return whether A and B are equal.}
    if not BaseField(A) eq BaseField(B) then
        return false;
    end if;

    if not A`extensions eq B`extensions then
        return false;
    end if;

    if not IsRealized(A) eq IsRealized(B) then
        return false;
    end if;

    if IsRealized(A) then
        if not A`realizingElements eq B`realizingElements then
            return false;
        end if;
    end if;

    return true;
end intrinsic;

intrinsic Basis(alg::AlgEta) -> SeqEnum[AlgEtaElt]
    {Calculate the standard Basis of alg over alg`baseField.

    It is given as the disjoint union over the bases for each field,
    using the standard Basis in each field respectively.}

    complete_basis := [];
    for i in [1..#alg`extensions] do
        basis_in_field := common_integral_basis(alg`extensions[i]);
        basis_of_this_field := [alg ! [
            (k eq i)
                select basis_in_field[j]
                else 0                  : k in [1..#alg`extensions]]
                                : j in [1..Degree(alg`extensions[i])]];
        complete_basis cat:= basis_of_this_field;
    end for;
    return complete_basis;
end intrinsic;

/// Try to carry the realization of old to new
///
/// INPUTS
///  EtaAlg old, new
///  Map[EtaAlg, EtaAlg] old_to_new
///  str mode in ["Drop", "Force", "Auto"]:
///     Drop: ignore the realization
///     Force: Return failure if realization cannot be moved
///     Auto: Return success, even if realization cannot be moved
/// OUTPUTs
///  bool (true iff the realization was moved or Drop or Auto was selected)
///  str (reason for boolness of first argument; human readable)
///  bool: The new algebra got a new realization
///  EtaAlg: new with the realization moved from old if that was possible
function move_realization(old, new, old_to_new, mode)
    if mode eq "Drop" then
        return true, "Realization not moved: Drop.", false, new;
    end if;

    if not IsRealized(old) then
        if mode eq "Force" then
            return false, "Original Algebra is not realized, cannot move the realization.", false, 0;
        elif mode eq "Auto" then
            return true, "Realization not moved: Auto.", false, new;
        end if;
    end if;

    is_sub, embed := IsSubfield(new`baseField, old`baseField);
    if not is_sub then
        if mode eq "Force" then
            return false,
                "New baseField is not embeddable in the old base field, cannot move the realization.",
                false, 0;
        elif mode eq "Auto" then
            return true, "Realization not moved: Auto.", false, new;
        end if;
    end if;

    old_realization, old_realization_map := RealizingAlgebra(old);
    // the new base is smaller then the old base. in particular,
    // old_to_new is new_base linear and old_realization_map is also new_base linear
    // so that realization_map will be new_base linear
    realization_map := map<new -> old_realization |
                           x :-> old_realization_map(Inverse(old_to_new)(x))>;
    realizing_elements := [realization_map(
                                new ! [(k eq i)
                                    select new`extensions[i].1
                                    else 0
                                  : i in [1..#new`extensions]])
                           : k in [1..#new`extensions]];
    new`realizingElements := realizing_elements;
    new`centralIdempotents := old`centralIdempotents;
    return true, "", true, new;
end function;

/// Try to carry the involution of old to new
///
/// INPUTS
///  EtaAlg old, new
///  Map[EtaAlg, EtaAlg] old_to_new
///  str mode in ["Drop", "Force", "Auto"]:
///     Drop: ignore the involution
///     Force: Return failure if involution cannot be moved
///     Auto: Return success, even if involution cannot be moved
/// OUTPUTs
///  bool (true iff the involution was moved or Drop or Auto was selected)
///  str (reason for boolness of first argument; human readable)
///  bool: The new algebra got a new involution
///  EtaAlg: new with the involution moved from old if that was possible
function move_involution(old, new, old_to_new, mode)
    if mode eq "Drop" then
        return true, "", false, new;
    end if;

    if not IsInvolutive(old) then
        if mode eq "Force" then
            return false, "Original Algebra is not involutive, cannot move the Involution.", 0;
        elif mode eq "Auto" then
            return true, "Involution not moved: Auto.", false, new;
        end if;
    end if;

    is_sub, embed := IsSubfield(new`baseField, old`baseField);
    if not is_sub then
        if mode eq "Force" then
            return false,
                "New baseField is not embeddable in the old base field, cannot move the Involution.",
                false, 0;
        elif mode eq "Auto" then
            return true, "Involution not moved: Auto.", false, new;
        end if;
    end if;

    // the new base is smaller then the old base. in particular,
    // old_to_new is new_base linear and _Conjugate (of old) is also new_base linear
    // so that involution will be new_base linear
    involution := map<new -> new |
                      x :-> old_to_new(_Conjugate(Inverse(old_to_new)(x)))>;
    images_of_field_generators := [involution(
        new ! [(k eq i) select new`extensions[i].1 else 0
               : i in [1..#new`extensions]])
                                   : k in [1..#new`extensions]];
    new`imagesOfFieldGenerators := images_of_field_generators;

    old_inv := InvolutiveRing(old`imageOfBaseFieldGenerator);
    conj := _Conjugate(old_inv ! new`baseField.1);
    assert2 IsCoercible(new, conj);
    ionbg_in_nb := new ! conj;

    is_coercible, tmp := IsInBaseField(ionbg_in_nb);
    assert is_coercible;
    new`imageOfBaseFieldGenerator := tmp;
    return true, "", true, new;
end function;

intrinsic RedefineOverNewField(alg::AlgEta, new_base_field::FldRat
        : realization:="Auto", involution:="Auto") -> AlgEta, Map[AlgEta, AlgEta]
    {Trivial redirect to FldNum version.}
    return RedefineOverNewField(alg, QNF());
end intrinsic;

intrinsic RedefineOverNewField(alg::AlgEta, new_base_field::FldNum
        : realization:="Auto", involution:="Auto") -> AlgEta, Map[AlgEta, AlgEta]
    {Given an etale algebra and a field embeddable into each summand,
    change the baseField of the algebra to the new base field.

    Note that the new field may be smaller or larger then the current baseField.

    Return also a map from the original to the new algebra.

    realization can be set to:
        "Force": Exit with an error if there is no natural way to carry the realization
            to the new algebra
        "Drop": Do not add a realization to the new algebra
        "Auto": Add a realization when possible, silently drop it when impossible
    Moving the realization is possible iff new_base_field is a subfield of baseField

    involution can be set to the same three values. Moving the involution is possible
    exactly iff moving the realization is possible}

    // the trivial algebra can always be trivially redefined.
    if Dimension(alg) eq 0 then
        res := EtaleAlgebra([], new_base_field);
        if IsRealized(alg) then
            res`realizingElements := alg`realizingElements;
            res`centralIdempotents := alg`centralIdempotents;
        end if;
        cast := map<alg -> res | x :-> res ! x, y :-> alg ! y>;
        return res, cast;
    end if;

    // first check that a redefinition is possible
    new_extensions := [**];
    casts := [**];
    for i in [1..#alg`extensions] do
        is_sub, emb := IsSubfield(new_base_field, alg`extensions[i]);
        require is_sub :
            "The new base field is not embeddable into each of the fields in this algebra.";

        // we have to keep new_field.1 equal to the original field definer up to coercion
        // which be do by extending by x-new_field.1 in the linear case
        if AbsoluteDegree(new_base_field) eq AbsoluteDegree(alg`extensions[i]) then
            new_field := ext<new_base_field |
                             Polynomial([-new_base_field.1,1]) :
                             DoLinearExtension:=true>;
        else
            new_field := relative_field_but_does_not_segfault(
                new_base_field, alg`extensions[i]);
        end if;
        is_iso, cast := IsIsomorphic(alg`extensions[i], new_field);
        assert is_iso;
        Append(~casts, cast);
        Append(~new_extensions, new_field);
    end for;
    assert2 forall{i : i in [1..#new_extensions] | BaseField(new_extensions[i]) eq new_base_field};
    assert2 forall{i : i in [1..#new_extensions] | IsCoercible(new_extensions[i], casts[i](alg`extensions[i].1))};

    res := New(AlgEta);
    res`baseField := new_base_field;
    res`originalFields := alg`originalFields;
    res`extensions := new_extensions;

    // the cast, tentative
    alg_to_res := map<alg -> res |
        x :-> res ! [*casts[i](Eltseq(x)[i]) : i in [1..#res`extensions]*],
        y :-> alg ! [*Inverse(casts[i])(Eltseq(y)[i]) : i in [1..#alg`extensions]*]>;

    // Deal with the realization
    success, msg, moved, res := move_realization(alg, res, alg_to_res, realization);
    require success : msg;

    // Deal with the involution
    success, msg, moved, res := move_involution(alg, res, alg_to_res, involution);
    require success : msg;

    // now construct the coercion map alg -> res
    // (we have to do redo this, because moving the realization and involution changes the object)
    alg_to_res := map<alg -> res |
        x :-> res ! [*casts[i](Eltseq(x)[i]) : i in [1..#res`extensions]*],
        y :-> alg ! [*Inverse(casts[i])(Eltseq(y)[i]) : i in [1..#alg`extensions]*]>;

    if GetAssertions() ge 3 then
        for b in Basis(alg) do
            assert3 forall{i : i in [1..#alg`extensions] | Parent(Eltseq(alg_to_res(b))[i]) eq res`extensions[i]};
            assert3 Inverse(alg_to_res)(alg_to_res(b)) eq b;
        end for;
    end if;

    assert Domain(alg_to_res) eq alg;
    assert Codomain(alg_to_res) eq res;

    return res, alg_to_res;
end intrinsic;

// functions relating to realization
intrinsic IsRealized(alg::AlgEta) -> BoolElt
    {Return whether alg has a realization associated.}
    return assigned alg`realizingElements;
end intrinsic;

intrinsic RealizingAlgebra(alg::AlgEta) -> Alg, Map[AlgEta, Alg]
    {Return the algebra realizing this AlgEta.}

    if Dimension(alg) eq 0 then
        return MatrixAlgebra(alg`baseField, 0);
    end if;

    require IsRealized(alg) :
        "Realization for this algebra is not set.";

    super_alg := Parent(alg`realizingElements[1]);
    realization := sub<super_alg | [alg`realizingElements[i]
                                    : i in [1..#alg`extensions]]>;

    running_to_pair := [];
    i := 1;
    while i le #alg`extensions do
        for j in [1..Degree(alg`extensions[i])] do
            Append(~running_to_pair, <i, j>);
        end for;
        i +:= 1;
    end while;

    basis_in_algebra := [ElementRealization(alg ! [
                            (k eq i) select alg`extensions[i].1^(j-1) else 0
                                                   : k in [1..#alg`extensions]])
                         : j in [1..Degree(alg`extensions[i])],
                            i in [1..#alg`extensions]];

    alg_to_realization := map<alg -> realization |
        x :-> ElementRealization(x),
        y :-> &+[alg ! [(running_to_pair[k][1] eq l)
                  select coordinates_in_basis(y, basis_in_algebra)[k]
                      * alg`extensions[l].1^(running_to_pair[k][2] - 1)
                  else 0
                        : l in [1..#alg`extensions]]
                 : k in [1..Dimension(realization)]]>;

    return realization, alg_to_realization;
end intrinsic;

intrinsic StandardRealization(alg::AlgEta
        : update_realization:=false) -> AlgMat, Map[AlgEta, AlgMat]
    {Calculate the standard realization of alg.

    This is a direct sum of standard realizations for each field.
    For each field E over K, use the left-regular representation of E in M_n(K).

    OUTPUTS
        the standard realizing algebra isomorphic to alg
        map from alg to the realization
    NOTES
        When update_realization is set to true, sets the realization of alg
        to be the standard realization, potentially overwriting an old realization}

    realization := MatrixAlgebra(alg`baseField, 0);

    if Dimension(alg) eq 0 then
        return realization, map<alg -> realization | x :-> x>;
    end if;

    generators := [**];
    positions := [];
    current_position := 1;
    for index in [1..#alg`extensions] do
        gen := left_reg_with_integral_basis(alg`extensions[index].1);
        gen := Matrix(alg`baseField, gen);
        new_algebra := MatrixAlgebra<alg`baseField, NumberOfRows(gen) | gen>;
        assert3 Dimension(new_algebra) eq Degree(alg`extensions[index]);
        Append(~generators, gen);
        Append(~positions, current_position);
        current_position +:= NumberOfRows(gen);
        realization := DirectSum(realization, new_algebra);
    end for;

    // construct the map from alg to realization
    running_to_pair := [];
    basis_in_realization := [];
    zero_in_real := realization ! 0;
    for i in [1..#alg`extensions], j in [1..Degree(alg`extensions[i])] do
        Append(~running_to_pair, <i, j>);
        tmp := zero_in_real;
        InsertBlock(~tmp, generators[i]^(j-1), positions[i], positions[i]);
        Append(~basis_in_realization, realization ! tmp);
    end for;

    assert2 #running_to_pair eq Dimension(realization);

    alg_to_realization := map<alg -> realization |
        x :-> &+[Eltseq(Eltseq(x)[running_to_pair[k][1]])[running_to_pair[k][2]]
                  * basis_in_realization[k] : k in [1..Dimension(realization)]],
        y :-> alg ! [*&+[(running_to_pair[k][1] eq i) select 
                        coordinates_in_basis(y, basis_in_realization)[k] *
                        alg`extensions[running_to_pair[k][1]].1^(running_to_pair[k][2] - 1)
                        else alg`extensions[i] ! 0
                        : k in [1..Dimension(realization)]]
                     : i in [1..#alg`extensions]*]>;

    if update_realization then
        // set the realization to the left regular we just calculated
        alg`realizingElements := [];
        alg`centralIdempotents := [];
        for i in [1..#alg`extensions] do
            tmp := zero_in_real;
            InsertBlock(~tmp, generators[i], positions[i], positions[i]);
            Append(~alg`realizingElements, realization ! tmp);

            tmp := zero_in_real;
            InsertBlock(~tmp, IdentityMatrix(alg`baseField,
                    NumberOfRows(generators[i])), positions[i], positions[i]);
            Append(~alg`centralIdempotents, realization ! tmp);
        end for;
    end if;

    // calculation done. final set of asserts
    assert ISA(Type(alg_to_realization), Map);
    if GetAssertions() ge 2 then
        for b in Basis(alg) do
            assert Evaluate(MinimalPolynomial(b), alg_to_realization(b)) eq 0;
        end for;
    end if;

    return realization, alg_to_realization;
end intrinsic;

intrinsic ElementRealization(x::AlgEtaElt) -> AlgElt
    {Given an element of a realized etale algebra, return its realization.}
    alg := Parent(x);
    require IsRealized(alg) :
        "Cannot realize an element in an unrealized algebra.";

    assert forall{i : i in [1..#alg`extensions] |
                  Evaluate(MinimalPolynomial(
                    alg`realizingElements[i]),
                    alg`extensions[i].1) eq 0};

    // we smash into the corner Algebra cMc to get the correct identity.
    res := &+[
        Eltseq(Eltseq(x)[i])[j] *
        alg`centralIdempotents[i] *
        alg`realizingElements[i]^(j-1) *
        alg`centralIdempotents[i]
              : j in [1..Degree(alg`extensions[i])], i in [1..#alg`extensions]];

    assert3 Evaluate(MinimalPolynomial(res), x) eq alg ! 0;
    return res;
end intrinsic;

// Functions relating to elements
intrinsic 'eq'(x::AlgEtaElt, y::AlgEtaElt) -> BoolElt
    {Return whether x and y are equal.}
    if not Parent(x) eq Parent(y) then
        return false;
    end if;

    if not Eltseq(x) eq Eltseq(y) then
        return false;
    end if;

    return true;
end intrinsic;

intrinsic Parent(x::AlgEtaElt) -> .
    {Parent of x}
    // Code: Return the parent of x
    return x`Parent;
end intrinsic;

intrinsic IsCoercible(algebra::AlgEta, y::Any) -> BoolElt, Any
    {Return whether y is coercible into algebra and the result if so}
    // Element of algebra
    if Type(y) eq AlgEtaElt and Parent(y) eq algebra then
        return true, y;
    end if;

    // [Any] in the correct fields
    if Type(y) eq SeqEnum or Type(y) eq List then
        if not #y eq #algebra`extensions then
            return false, "Input has wrong length.";
        end if;

        if not forall{i : i in [1..#y] | IsCoercible(algebra`extensions[i], y[i])} then
            return false, "Entries of input must be coercible into the fields in the algebra at each index.";
        end if;

        res := New(AlgEtaElt);
        res`Parent := algebra;
        res`entries := [**];
        for i in [1..#algebra`extensions] do
            x := algebra`extensions[i] ! y[i];
            Append(~res`entries, x);
        end for;
        return true, res;
    end if;

    // Anything that is coercible into BaseField(algebra), but not a List / SeqEnum
    if IsCoercible(BaseField(algebra), y) then
        res := New(AlgEtaElt);
        res`Parent := algebra;
        res`entries := [*algebra`extensions[i] ! y : i in [1..#algebra`extensions]*];
        return true, res;
    end if;
    return false, Sprintf("Coercion is not implemented or impossible. Got %o", Type(y));
end intrinsic;

intrinsic 'in'(e::., algebra::AlgEta) -> BoolElt
    {Return whether e is in algebra}
    is_coercible, coercion := IsCoercible(algebra, e);
    return is_coercible;
end intrinsic;

intrinsic SubConstructor(algebra::AlgEta, t::.) -> T
    {Return the substructure of algebra generated by elements of the tuple t}
    // This corresponds to the constructor call sub<algebra | r1, r2, ..., rn>
    // t is ALWAYS a tuple of the form <r1, r2, ..., rn>
    // Code: do tests on the elements in t to see whether valid and then
    //       set S to the substructure of T generated by r1, r2, ..., rn
    // Use standard require statements for error checking
    // Possibly use "t := Flat(t);" to make it easy to loop over t if
    //     any of the ri are sequences
    error "Not Implemented: AlgEta is an abstract algebra, subalgebras cannot be calculated such that they are coercible.";
end intrinsic;

intrinsic SubFromMask(algebra::AlgEta, mask::[BoolElt]) -> AlgEta, Map[AlgEta, AlgEta]
    {Given an etale algebra and a mask, create the algebra from the fields for which the mask is true.

    Create also the natural injection/projection from/to the new sub to/from algebra.

    OUTPUTs:
        EtaAlg: the new subalgebra
        Map[EtaAlg, EtaAlg]: the map from the new sub to algebra. Is an injection. Is invertible.}

    require #mask eq #algebra`extensions : "The mask must have equal length to the algebra.";

    indices := [i : i in [1..#algebra`extensions] | mask[i]];

    res := New(AlgEta);
    res`baseField := algebra`baseField;
    res`extensions := [algebra`extensions[i] : i in indices];
    res`originalFields := [algebra`originalFields[i] : i in indices];

    inject_project := map<
        res -> algebra |
        x :-> algebra ! [*(i in indices) select Eltseq(x)[Index(indices, i)] else 0 : i in [1..#algebra`extensions]*],
        y :-> res ! [*Eltseq(y)[i] : i in indices*]>;

    if IsRealized(algebra) then
        res`realizingElements := [
            algebra`realizingElements[i]
            : i in indices];
        res`centralIdempotents := [
            algebra`centralIdempotents[i]
            : i in indices];
    end if;

    if IsInvolutive(algebra) then
        res`imagesOfFieldGenerators := [
            Inverse(inject_project)(algebra`imagesOfFieldGenerators[i])
            : i in indices];
        res`imageOfBaseFieldGenerator := algebra`imageOfBaseFieldGenerator;
    end if;

    return res, inject_project;
end intrinsic;

intrinsic Print(x::AlgEtaElt)
    {Print for AlgEtaElt.}
    printf "%o", x`entries, "Magma";
end intrinsic;

intrinsic '#'(x::AlgEtaElt) -> RngIntElt
    {Return the Number of Fields in Parent(x)}
    return #x`entries;
end intrinsic;

intrinsic Eltseq(x::AlgEtaElt) -> SeqEnum[FldNumElt]
    {Return the entries of x}
    return x`entries;
end intrinsic;

intrinsic '+'(x::AlgEtaElt, y::AlgEtaElt) -> AlgEtaElt
    {Add the two elements pairwise.}
    require Parent(x) eq Parent(y) :
        "Elements live in different algebras.";
    return Parent(x) ! [*Eltseq(x)[i] + Eltseq(y)[i] : i in [1..#x]*];
end intrinsic;

intrinsic '-'(x::AlgEtaElt, y::AlgEtaElt) -> AlgEtaElt
    {Subtract the two elements pairwise.}
    require Parent(x) eq Parent(y) :
        "Elements live in different algebras.";
    return Parent(x) ! [*Eltseq(x)[i] - Eltseq(y)[i] : i in [1..#x]*];
end intrinsic;

intrinsic '-'(x::AlgEtaElt) -> AlgEtaElt
    {Subtract the two elements pairwise.}
    return Parent(x) ! [*-Eltseq(x)[i] : i in [1..#x]*];
end intrinsic;

intrinsic '*'(x::AlgEtaElt, y::AlgEtaElt) -> AlgEtaElt
    {Multiply the two elements pairwise.}
    require Parent(x) eq Parent(y) :
        "Elements live in different algebras.";
    return Parent(x) ! [*Eltseq(x)[i] * Eltseq(y)[i] : i in [1..#x]*];
end intrinsic;

intrinsic '/'(x::AlgEtaElt, y::AlgEtaElt) -> AlgEtaElt
    {Divide the two elements pairwise.}
    require Parent(x) eq Parent(y) :
        "Elements live in different algebras.";
    require forall{i : i in [1..#x] | not Eltseq(y)[i] eq 0} :
        "Cannot divide by zerodivisor.";
    return Parent(x) ! [*Eltseq(x)[i] / Eltseq(y)[i] : i in [1..#x]*];
end intrinsic;

intrinsic PowerRespectSubalgebra(x::AlgEtaElt, n::RngIntElt) -> AlgEtaElt
    {Like the normal power map, but take the power individually in each component.
    Thus, If x is 0 at a field, do not return 1 there.}
    return Parent(x) ! [*(Eltseq(x)[i] eq 0) select 0 else Eltseq(x)[i]^n : i in [1..#x]*];
end intrinsic;

intrinsic '^'(x::AlgEtaElt, n::RngIntElt) -> AlgEtaElt
    {Calculate the Power of an element.}
    return Parent(x) ! [*Eltseq(x)[i]^n : i in [1..#x]*];
end intrinsic;

// scalar arithmetic
intrinsic '*'(x::FldNumElt, y::AlgEtaElt) -> AlgEtaElt
    {Scalar multiplication from the left.}
    require Parent(x) eq BaseField(Parent(y)) :
        "Can only multiply by elements of the base field.";
    return Parent(y) ! [*x * Eltseq(y)[i] : i in [1..#y]*];
end intrinsic;

intrinsic '*'(x::AlgEtaElt, y::FldNumElt) -> AlgEtaElt
    {Scalar multiplication from the right.}
    return y * x;
end intrinsic;

intrinsic '*'(x::FldRatElt, y::AlgEtaElt) -> AlgEtaElt
    {Scalar multiplication from the left.}
    return Parent(y) ! [*x * Eltseq(y)[i] : i in [1..#y]*];
end intrinsic;

intrinsic '*'(x::AlgEtaElt, y::FldRatElt) -> AlgEtaElt
    {Scalar multiplication from the right.}
    return y * x;
end intrinsic;

intrinsic '*'(x::RngIntElt, y::AlgEtaElt) -> AlgEtaElt
    {Scalar multiplication from the left.}
    require IsCoercible(Parent(y), x) :
        "Cannot coerce the lhs into the parent of the rhs.";
    return Parent(y) ! [*x * Eltseq(y)[i] : i in [1..#y]*];
end intrinsic;

intrinsic '*'(x::AlgEtaElt, y::RngIntElt) -> AlgEtaElt
    {Scalar multiplication from the right.}
    return y * x;
end intrinsic;

intrinsic ElementLiesInSubfield(x::AlgEtaElt) -> BoolElt, RngIntElt
    {If x lies completely in one of the subfields, return true and its index.
    Return false, 0 otherwise.}
    index := 0;
    for i in [1..#x] do
        if not Eltseq(x)[i] eq 0 then
            if index eq 0 then
                index := i;
                continue i;
            end if;
            return false, 0;
        end if;
    end for;
    return not index eq 0, index;
end intrinsic;

intrinsic Evaluate(f::RngUPolElt, x::AlgEtaElt) -> AlgEtaElt
    {Evaluate f(x).}

    require IsSubfield(BaseRing(Parent(f)), Parent(x)`baseField) :
        "The polynomial must be defined over the algebras baseField.";

    return &+[(Parent(x) ! Eltseq(f)[i]) * x^(i-1) : i in [1..Degree(f)+1]];
end intrinsic;

intrinsic MinimalPolynomial(x::AlgEtaElt) -> RngUPolElt
    {Calculate the MinimalPolynomial of the element.

    This is the LCM of all the different minimal polynomials of the entries.}
    if #x eq 0 then
        return PolynomialRing(Integers()) ! 0;
    end if;

    curr := MinimalPolynomial(x`entries[1]);
    for j in [2..#x] do
        curr := LeastCommonMultiple(curr, MinimalPolynomial(x`entries[j]));
    end for;
    return curr;
end intrinsic;

intrinsic IsInBaseField(x::AlgEtaElt) -> BoolElt, FldNumElt
    {If x lies in 1*BaseField(Parent(x)), return it as a FldNumElt.

    OUTPUTs:
        bool (x lies in 1 * BaseField(Parent(x)))
        FldNumElt x coerced into BaseField(Parent(x))}

    alg := Parent(x);
    if Dimension(alg) eq 0 then
        return false, BaseField(alg) ! 0;
    end if;

    is_coercible, curr := IsCoercible(BaseField(alg), Eltseq(x)[1]);
    if not is_coercible then
        return false, BaseField(alg) ! 0;
    end if;

    for i in [2..#alg`extensions] do
        is_coercible, next := IsCoercible(BaseField(alg), Eltseq(x)[i]);
        if not is_coercible then
            return false, BaseField(alg) ! 0;
        end if;
        if not next eq curr then
            return false, BaseField(alg) ! 0;
        end if;
    end for;
    return true, curr;
end intrinsic;
