// Definition for AlgebraicTorus and bookkeeping / wrapper functions for that type

import "../core/primitives.m" :
    find_smallest_prime_with_good_reduction_in_field,
    relative_field_but_does_not_segfault,
    left_reg_with_integral_basis,
    decomposition_but_works,
    corresponding_irred;
import "../core/characters.m" :
    ranks_of_irreds;

declare type AlgTor;

declare attributes AlgTor:
    // The field over which all the Irreducibles are defined
    baseField,
    // The AlgebraicTorusIrreds
    irreducibles,

    // OPTIONAL values concerned with the realization of a torus.
    // The image of irred`extensionField.1 in the realizing algebra
    // the complete map is then just the embedding of finite field extensions of baseField
    // into the images Parent.
    realizingElements,
    // the central idempotent, whose smash the realizerImage lies in
    centralIdempotents,

    // An element of irred`extensionField whose Zariski-Closure is the irreducible
    // (i.e. of infinite order and inside of the irred)
    generators
;

// Constructors
intrinsic AlgebraicTorus(base_field::FldNum) -> AlgTor
    {Create a trivial Torus.}

    require BaseRing(base_field) eq Rationals() :
        "base_field must be defined over Rationals()";
    torus := New(AlgTor);
    torus`baseField := base_field;
    torus`irreducibles := [];
    torus`realizingElements := [];
    torus`centralIdempotents := [];

    return torus;
end intrinsic;

intrinsic AlgebraicTorus(base_field::FldRat) -> AlgTor
    {Create a trivial Torus over Rationals().}
    torus := New(AlgTor);
    torus`baseField := QNF();
    torus`irreducibles := [];
    return torus;
end intrinsic;

intrinsic AlgebraicTorus(
        list_of_irreds::[AlgTorIrr] :
        realizing_elements:=false,
        central_idempotents:=false) -> AlgTor
    {Create the AlgebraicTorus built from the given irreducibles.}

    // input validation
    require #list_of_irreds gt 0 :
        "Empty List of irreducibles is not allowed because I can not determine the baseField.";
    base_field := list_of_irreds[1]`baseField;
    for irred in list_of_irreds do
        require irred`baseField eq base_field or (Degree(base_field) eq 1 and Degree(irred`baseField) eq 1) :
            "The base fields of all irreducibles must be equal.";
    end for;

    if not realizing_elements cmpeq false then
        require Type(realizing_elements) eq SeqEnum :
            "realizing_elements must be SeqEnum.";
        require forall{x
                       : x in realizing_elements
                       | ISA(Type(x), AlgMatElt)} :
            "The realizers must be AlgMatElts.";
        require Type(central_idempotents) in [SeqEnum] :
            "realizing_elements is given, so central_idempotents must also be given (as SeqEnum or List).";
        require #central_idempotents eq #list_of_irreds :
            "For each irred, one realizing image must be given";
        require Universe(central_idempotents) eq Universe(realizing_elements) :
            "central_idempotents and realizing_elements must have the same Universe.";
    end if;

    res := New(AlgTor);
    res`baseField := base_field;
    res`irreducibles := list_of_irreds;
    res`realizingElements := realizing_elements;
    res`centralIdempotents := central_idempotents;

    return res;
end intrinsic;

intrinsic AlgebraicTorus(base_field::FldNum,
                 fixed_field::FldNum,
                 extension_field::FldNum :
                 Prime:=0,
                 realizing_element:=false,
                 central_idempotent:=false) -> AlgTor
    {Create the full AlgebraicTorus given by a field tower.}

    // Check that base_field is defined over Q
    require BaseRing(base_field) eq Rationals():
        "base_field must be defined over Rationals()";
    // Check that fixed_field | base_field
    require BaseRing(fixed_field) eq base_field:
        "fixed_field must be defined over base_field";
    // Check that either extension_field is equal to fixed_field or
    // defined over it of degree 1 or 2
    if not extension_field eq fixed_field then
        // Check that extension_field | fixed_field
        require BaseRing(extension_field) eq fixed_field:
            "extension_field must be defined over fixed_field or equal to it.";
        require Degree(extension_field, fixed_field) in [1, 2] :
            "The Degree of extension_field over fixed_field must be 1 or 2";
    end if;

    if not realizing_element cmpeq false then
        require not central_idempotent cmpeq false :
            "realizing_element is given, so central_idempotent must also be given.";
        require Parent(realizing_element) eq Parent(central_idempotent) :
            "realizing_element and central_idempotent must have the same parent.";
    end if;

    if Prime eq 0 then
        Prime := find_smallest_prime_with_good_reduction_in_field(extension_field);
    end if;
    place_in_base_field_over_prime := Decomposition(base_field, Prime)[1][1];

    irreds, ranks, collateral_data := ranks_of_irreds(
        base_field, fixed_field, extension_field, [place_in_base_field_over_prime]);

    // create the information for the realization
    if not realizing_element cmpeq false then
        // manual realization
        realizer_gen := realizing_element;
        idempotent := central_idempotent;
        realizer_alg := Parent(realizer_gen);
    elif AbsoluteDegree(extension_field) eq AbsoluteDegree(fixed_field) then
        // the swap-case
        M_n_BF := MatrixAlgebra(base_field, Degree(fixed_field, base_field));
        M_n_BF_2 := DirectSum(M_n_BF, M_n_BF);

        // calculate the image of extension_field in the matrix algebra.
        // we have to redefine extension_field over base_field
        tmp := relative_field_but_does_not_segfault(base_field, fixed_field);
        realizer_gen_in_FF := left_reg_with_integral_basis(tmp.1);

        realizer_gen := DirectSum(
            M_n_BF ! realizer_gen_in_FF, M_n_BF ! realizer_gen_in_FF^-1);
        realizer_alg := M_n_BF_2;
        idempotent := M_n_BF_2 ! 1;
    else
        // the ext-case
        M_n_BF := MatrixAlgebra(base_field, Degree(extension_field, base_field));

        // calculate the image of extension_field in the matrix algebra.
        // we have to redefine extension_field over base_field
        tmp := relative_field_but_does_not_segfault(base_field, extension_field);
        realizer_gen := M_n_BF ! left_reg_with_integral_basis(tmp.1);
        assert3 Evaluate(MinimalPolynomial(realizer_gen), tmp.1) eq 0;
        realizer_alg := M_n_BF;
        idempotent := M_n_BF ! 1;
    end if;
    realizing_elements := [realizer_alg | realizer_gen : i in [1..#irreds]];
    central_idempotents := [realizer_alg | idempotent : i in [1..#irreds]];


    // create the Torus from the calculated irreducible charactermodules
    list_of_irreds := [];
    for index in [1..#irreds] do
        irred := irreds[index];
        this_irred_as_AlgebraicTorusIrred := AlgebraicTorusIrred(
            [base_field,
            fixed_field,
            extension_field],
            irred,
            collateral_data);
        _CacheGlobalRank(
            this_irred_as_AlgebraicTorusIrred,
            ranks[index][0]);
        _CacheRank(
            this_irred_as_AlgebraicTorusIrred,
            place_in_base_field_over_prime,
            ranks[index][1]);
        Append(~list_of_irreds, this_irred_as_AlgebraicTorusIrred);
    end for;

    return AlgebraicTorus(
        list_of_irreds :
        realizing_elements:=realizing_elements,
        central_idempotents:=central_idempotents);
end intrinsic;

intrinsic AlgebraicTorus(base_field::FldRat,
                 fixed_field::FldNum,
                 extension_field::FldNum :
                 Prime:=0) -> AlgebraicTorus
    {Create a torus with the baseField Rationals()}
    Q := QNF();
    _ := IsSubfield(Q, fixed_field);
    fixed_field := relative_field_but_does_not_segfault(Q, fixed_field);
    _ := IsSubfield(fixed_field, extension_field);
    extension_field := relative_field_but_does_not_segfault(fixed_field, extension_field);
    // Call the version where Q is FldNum instead of FldRat
    return AlgebraicTorus(Q, fixed_field, extension_field : Prime:=Prime);
end intrinsic;

intrinsic AlgebraicTorus(base_field::FldRat,
                 fixed_field::FldRat,
                 extension_field::FldNum :
                 Prime:=0) -> AlgebraicTorus
    {Create a torus with the baseField and fixedField Rationals()}
    Q := QNF();
    Q2 := ext<Q | Polynomial([-1, 1]) : DoLinearExtension:=true>;
    _ := IsSubfield(Q2, extension_field);
    extension_field := relative_field_but_does_not_segfault(Q2, extension_field);
    // Call the version where base_ and fixed_field are FldNum instead of FldRat
    return AlgebraicTorus(Q, Q2, extension_field : Prime:=Prime);
end intrinsic;

intrinsic DirectProduct(A::AlgTor, B::AlgTor :
                        realization_internal_direct:=false) -> AlgTor
    {Build the Direct Product A times B

    INPUTS
        AlgTor A
        AlgTor B
        BoolElt realization_internal_direct=false:
            if true: the realization is an internal direct product;
                both Tori must be realized in the same algebra
            if false: the realization is the external direct product;
                the Tori may be realized in different algebras
    OUTPUTS
        The direct Product with all irreducibles of A listed before
            all the irreducibles of B
    NOTES
        if either Torus is not realized, the product will not be realized,
        independent of realization_internal_direct.}
    require A`baseField eq B`baseField or (Degree(A`baseField) eq 1 and Degree(B`baseField) eq 1):
        "The two Tori must have the same baseField.";
    require ISA(Type(realization_internal_direct), BoolElt) :
        "realization_internal_direct must be BoolElt";

    // the irreducibles can simply be appended to each other
    new_irreds := A`irreducibles cat B `irreducibles;

    // the realization is a little more complicated
    if IsRealized(A) and IsRealized(B) then
        real_A := Universe(A`realizingElements);
        real_B := Universe(B`realizingElements);
        if realization_internal_direct then
            require real_A eq real_B :
                "realization_internal_direct is true, so the realizations must be equal.";
            total_realizing_algebra := real_A;
            new_realizing_elements := A`realizingElements cat B`realizingElements;
            new_idempotents := A`centralIdempotents cat B`centralIdempotents;
        else
            total_realizing_algebra := DirectSum(real_A, real_B);
            new_realizing_elements := [DirectSum(el, real_B ! 0) : el in A`realizingElements] cat
                                   [DirectSum(real_A ! 0, el) : el in B`realizingElements];
            new_idempotents := [DirectSum(el, real_B ! 0) : el in A`centralIdempotents] cat
                               [DirectSum(real_A ! 0, el) : el in B`centralIdempotents];
        end if;
    else
        new_realizing_elements := false;
        new_idempotents := false;
    end if;

    return AlgebraicTorus(new_irreds :
                          realizing_elements:=new_realizing_elements,
                          central_idempotents:=new_idempotents);
end intrinsic;

intrinsic DirectProduct(list_of_tori::[AlgTor] :
                        realization_internal_direct:=false) -> AlgTor
    {Create the direct product over a list of tori}
    require #list_of_tori gt 0 : "The trivial torus is not currently implemented.";

    require forall{el : el in list_of_tori | el`baseField eq list_of_tori[1]`baseField} :
        "All tori in the list must have the same baseField";

    torus := list_of_tori[1];
    for i in [2..#list_of_tori] do
        torus := DirectProduct(torus, list_of_tori[i] :
                               realization_internal_direct:=realization_internal_direct);
    end for;
    return torus;
end intrinsic;

intrinsic Dimension(torus::AlgTor) -> RngIntElt
    {Get the total dimension of the torus.}
    if #torus`irreducibles eq 0 then
        return 0;
    end if;
    return &+[Dimension(irred) : irred in torus`irreducibles];
end intrinsic;

intrinsic Print(torus::AlgTor)
    {Print for the AlgTor Type.}
    printf "Algebraic torus defined over %o of total dimension %o.", torus`baseField, Dimension(torus);
end intrinsic;

intrinsic AlgebraicTorus(base_field::FldNum,
                         etale_algebra::[<>] :
                         Prime:=0,
                         realizing_elements:=false,
                         central_idempotents:=false) -> AlgTor
    {Create an Algebraic Torus from an Etale Algebra.

    INPUTS
        FldNum base_field : the field over which the Torus is to be defined.
        List[Tuple<FldNum fixed_field, FldNum extension_field>]: the List defining the Etale Algebra
            The Algebra is the direct sum of Entries.
            A single entry either yields extension_field, when it is larger then fixed_field
                           or fixed_field + fixed_field, when they are equal.
            fixed_field must be defined over base_field.
            extension_field must be defined over fixed_field or be equal to it.
            [extension_field : fixed_field] must be 1 or 2.
    NOTES
        Will automatically determine the involution to use. Given the Algebra E,
        The Torus SU(E, τ) is created.
        τ is either - the nontrivial involution extension_field | fixed_field
             or     - the swap-type involution on two copies of fixed_field when extension_field eq fixed_field
    OPTIONS
        Prime: do local calculations over Prime if possible
        realizing_elements: for each tuple in etale_algebra, this should be an AlgMatElt
            which defines the image of (extension_field|base_field).1 under the realization
        central_idempotents: for each tuple in etale_algebra, this should be an AlgMatElt
            which defines the central idempotent of the subalgebra that this single field is realized in
    }

    if not realizing_elements cmpeq false then
        require not central_idempotents cmpeq false:
            "realizing_elements is given, so central_idempotents must also be given";
        require Universe(realizing_elements) eq Universe(central_idempotents) :
            "The universe of realizing_elements and central_idempotents must be equal";
    end if;

    if #etale_algebra eq 0 then
        res := AlgebraicTorus(base_field);
        if not realizing_elements cmpeq false then
            res`realizingElements := [Universe(realizing_elements) |];
            res`centralIdempotents := [Universe(central_idempotents) |];
        end if;
        return res;
    end if;

    if realizing_elements cmpeq false then
        return DirectProduct([
            AlgebraicTorus(base_field, etale_algebra[i][1], etale_algebra[i][2])
                              : i in [1..#etale_algebra]]);
    end if;

    return DirectProduct([
        AlgebraicTorus(base_field, etale_algebra[i][1], etale_algebra[i][2] :
                       realizing_element:=realizing_elements[i],
                       central_idempotent:=central_idempotents[i])
                          : i in [1..#etale_algebra]] :
                         realization_internal_direct:=true);
end intrinsic;

intrinsic AlgebraicTorus(base_field::FldRat,
                         etale_algebra::[<>] :
                         Prime:=0,
                         realizing_elements:=false,
                         central_idempotents:=false) -> AlgTor
    {Trivial Overload for Q-defined etale-algebras.}
    Q := QNF();
    // redefine the etale-algebra over Q
    etale_algebra_over_Q := [];
    for tower in etale_algebra do
        _ := IsSubfield(Q, tower[1]);
        fixed_field := relative_field_but_does_not_segfault(Q, tower[1]);
        _ := IsSubfield(fixed_field, tower[2]);
        extension_field := relative_field_but_does_not_segfault(fixed_field, tower[2]);
        Append(~etale_algebra_over_Q, <fixed_field, extension_field>);
    end for;

    return AlgebraicTorus(
        Q, etale_algebra_over_Q :
        Prime:=Prime,
        realizing_elements:=realizing_elements,
        central_idempotents:=central_idempotents);
end intrinsic;

intrinsic AlgebraicTorus(alg::AlgEta) -> AlgTor
    {Constructor from Involutive Etale Algebra.

    Trivial Redirect to SUOfInvolution(AlgEtaInv).}
    return SUOfInvolutiveEtaleAlgebra(alg);
end intrinsic;

intrinsic IsIsomorphicToSubTorus(A::AlgTor, B::AlgTor) -> BoolElt
    {Check whether all componentes of A appear in B.}
    if not (A`baseField eq B`baseField) and not (Degree(A`baseField) eq 1 and Degree(B`baseField) eq 1) then
        return false;
    end if;

    for irred in A`irreducibles do
        for b_irred in B`irreducibles do
            if IsIsomorphic(irred, b_irred) then
                continue irred;
            end if;
        end for;
        // this irreducible of A was not found in B.
        return false;
    end for;
    return true;
end intrinsic;

intrinsic IsIsomorphic(A::AlgTor, B::AlgTor) -> BoolElt
    {Check if the two tori have the same isomorphic components.}
    if not (A`baseField eq B`baseField) and not (Degree(A`baseField) eq 1 and Degree(B`baseField) eq 1) then
        return false;
    end if;

    return IsIsomorphicToSubTorus(A, B) and IsIsomorphicToSubTorus(B, A);
end intrinsic;

intrinsic WeilRestriction(torus::AlgTor, new_base_field::FldNum) -> AlgTor
    {Weil restrict A to a new baseField.}
    new_base_field := AbsoluteField(new_base_field);
    require new_base_field subset torus`baseField :
        "The new baseField must a subset of the old one.";
    list_of_tori := [];
    for irred in torus`irreducibles do
        restriction := WeilRestriction(irred, new_base_field);
        list_of_tori cat:= restriction`irreducibles;
    end for;
    return AlgebraicTorus(list_of_tori);
end intrinsic;

intrinsic WeilRestriction(torus::AlgTor, new_base_field::FldRat) -> AlgTor
    {Trivial overload of the version where new_base_field is FldRat.}
    return WeilRestriction(torus, QNF());
end intrinsic;

intrinsic _IrredsByIsomorphicFieldTower(torus::AlgTor) -> SeqEnum
    {group irreds into distinct (up to isomorphism) field towers}
    irreds_by_isomorphic_field_tower := [];
    for irred in torus`irreducibles do
        for ig_index in [1..#irreds_by_isomorphic_field_tower] do
            if FieldTowersAreIsomorphic(irred, irreds_by_isomorphic_field_tower[ig_index][1]) then
                // The list of irreducibles is already reduced up to isomorphism of G-Modules
                // so we do not have to re-reduce it here
                // (i.e. irreds_by_isomorphic_field_tower will contain no isomorphic tori)
                Append(~irreds_by_isomorphic_field_tower[ig_index], irred);
                continue irred;
            end if;
        end for;
        // This irreds field tower has no group yet. Make a new one.
        Append(~irreds_by_isomorphic_field_tower, [irred]);
    end for;
    return irreds_by_isomorphic_field_tower;
end intrinsic;

intrinsic LocalRank(torus::AlgTor, place::Any) -> RngIntElt
    {Calculate the local rank of the torus at place.

    INPUTS
        AlgTor torus
        Any place in torus`baseField
            - either PlcNumElt
            - or baseField=Q and place is a finite prime in RngInt or Infinity() 
    OUTPUTS
        RngIntElt rk_place(torus).
    NOTES
        While this function uses the fact that rk_p(T) is the sum of ranks of its irreds,
        we implement the logic on AlgTor instead of AlgTorIrr.
        This means that GaloisGroup will only be used once for each distinct field tower making up torus.
        Otherwise GaloisGroup would have to run once for each AlgTorIrr.}
    // Input validation and conversion: place
    if not Type(place) eq PlcNumElt then
        if place cmpeq Infinity() then
            require AbsoluteDegree(torus`baseField) eq 1 :
                "The place can only be specified as Infinity() when the baseField is isomorphic to Q.";
            place := InfinitePlaces(torus`baseField)[1];
        elif IsCoercible(Integers(), place) then
            require AbsoluteDegree(torus`baseField) eq 1 :
                "The place can only be specified as a finite prime when the baseField is isomorphic to Q.";
            require IsPrime(place) :
                "If given as a finite integer, the prime must be prime.";
            place := decomposition_but_works(torus`baseField, Integers() ! place)[1][1];
        else
            require false:
                "the place may only be given as PlcNumElt, Infinity() or a finite prime.";
        end if;
    else
        // place must be over torus`baseField
        require NumberField(place) eq torus`baseField :
            "place must be over torus`baseField.";
    end if;

    irreds_by_isomorphic_field_tower := _IrredsByIsomorphicFieldTower(torus);

    total_rank_at_place := 0;
    // run ranks_of_irreds for each such tower
    for ig_index in [1..#irreds_by_isomorphic_field_tower] do
        // get a representative of the field towers isomorphism class
        field_tower_class_rep := irreds_by_isomorphic_field_tower[ig_index][1];
        // and run ranks_of_irreds on it
        irreds, ranks, collateral_data := ranks_of_irreds(
            field_tower_class_rep`baseField,
            field_tower_class_rep`fixedField,
            field_tower_class_rep`extensionField,
            [place]);
        for irred in irreds_by_isomorphic_field_tower[ig_index] do
            has_corresponding_irred, irr_ind := corresponding_irred(
                irred`characterModule, irred`collateralData,
                irreds, collateral_data);
            if not has_corresponding_irred then
                "START DEBUG OUTPUT"; irred`characterModule; "searched in:"; irreds; "place"; place;
                "No module isomorphic to this irred was found, this is impossible.";
                assert false;
            end if;
            // this is the place-rank of irred with multiplicity
            total_rank_at_place +:= ranks[irr_ind][1];
            // Cache this result
            _CacheGlobalRank(irred, ranks[irr_ind][0]);
            _CacheRank(irred, place, ranks[irr_ind][1]);
        end for;
    end for;
    // return the sum
    return total_rank_at_place;
end intrinsic;

intrinsic GlobalRank(A::AlgTor) -> RngIntElt
    {Calculate the global rank of A (i.e. the A`baseField rank).

    This chooses a prime unramified in all extension fields of A,
    calculates LocalRank and then returns the cached global Rank.}

    p := 2;
    while true do
        p := NextPrime(p);
        if forall{irred : irred in A`irreducibles |
                  &+[el[2] - 1 : el in decomposition_but_works(irred`extensionField, p)] eq 0} then
            break;
        end if;
    end while;

    _ := LocalRank(A, p);
    return &+[GlobalRank(irred) : irred in A`irreducibles];
end intrinsic;

intrinsic BaseField(A::AlgTor) -> FldNum
    {Return the baseField.}
    return A`baseField;
end intrinsic;

intrinsic BaseRing(A::AlgTor) -> FldNum
    {Redirect for consistency.}
    return BaseField(A);
end intrinsic;

intrinsic Hash(A::AlgTor) -> RngIntElt
    {Hash the irreducibles and their multiplicity.}

    list_of_raw_infos := [*"TYPE::AlgTor", Hash(A`baseField)*];
    for irred in A`irreducibles do
        Append(~list_of_raw_infos, Hash(irred));
    end for;
    return Hash(list_of_raw_infos);
end intrinsic;

intrinsic 'eq'(A::AlgTor, B::AlgTor) -> BoolElt
    {Check two AlgTor for equality.}
    return Hash(A) eq Hash(B);
end intrinsic;

intrinsic IsRealized(A::AlgTor) -> BoolElt
    {true iff A has a realization set.}
    return assigned A`realizingElements;
end intrinsic;

intrinsic CalculateAllGenerators(torus::AlgTor)
    {For each irreducible, calculate a generator.}

    if assigned torus`generators then
        return;
    end if;

    torus`generators := [];
    for i in [1..#torus`irreducibles] do
        gen := ArbitraryGenerator(torus`irreducibles[i]);
        Append(~torus`generators, gen);
    end for;
end intrinsic;

function _generator_at_index(torus, index)
    // Given
    //  - a realized Torus whose generators are known and an index,
    // Calculate
    //  - the generator in the realizing algebra

    assert IsRealized(torus);
    assert assigned torus`generators;
    assert index in [1..#torus`irreducibles];

    EF_o_BF := relative_field_but_does_not_segfault(
        torus`irreducibles[index]`baseField,
        torus`irreducibles[index]`extensionField);

    gen_in_EF_o_BF := EF_o_BF ! torus`generators[index];

    realizer_gen := &+[
        Eltseq(gen_in_EF_o_BF)[j]
        * torus`centralIdempotents[index]
        * torus`realizingElements[index]^(j-1)
        * torus`centralIdempotents[index]
                       : j in [1..Degree(EF_o_BF)]];

    return realizer_gen;
end function;

intrinsic FullRealizingAlgebra(torus::AlgTor) -> AlgMat
    {Given a realization of a torus in internal format,
    calculate the complete Algebra created by this realization.}

    require IsRealized(torus) :
        "Cannot realized an unrealized torus.";

    CalculateAllGenerators(torus);

    realizing_algebra := Universe(torus`realizingElements);

    // add the first part for all realizers
    generators_of_full_algebra := [];
    for index in [1..#torus`irreducibles] do
        gen_in_alg := _generator_at_index(torus, index);
        assert gen_in_alg in realizing_algebra;
        Append(~generators_of_full_algebra, gen_in_alg);
    end for;

    // now create the subalgebra from these generators
    return sub<realizing_algebra | generators_of_full_algebra>;
end intrinsic;

intrinsic _SingleIrreducibleAsAlgTor(torus::AlgTor, index::RngIntElt) -> AlgTor
    {Get the index'th irreducible as a torus, copying all relevant information.}

    if IsRealized(torus) then
        realizing_elements := [torus`realizingElements[index]];
        central_idempotents := [torus`centralIdempotents[index]];
    else
        realizing_elements := false;
    end if;
    res := AlgebraicTorus([torus`irreducibles[index]] :
                          realizing_elements:=realizing_elements,
                          central_idempotents:=central_idempotents);

    if assigned torus`generators then
        res`generators := [torus`generators[index]];
    end if;
    return res;
end intrinsic;

intrinsic SIsotropicDecomposition(torus::AlgTor, set_of_places::SeqEnum[PlcNumElt]) -> AlgTor, AlgTor
    {Decompose torus into the maximal S-isotropic part and the remainder.}

    require forall{x : x in set_of_places | NumberField(x) eq torus`baseField} :
        "All places must be given as PlcNumElt in the baseField";

    // calculate all the ranks
    // it is more efficient to calculate (and cache) them all at once
    for p in set_of_places do
        _ := LocalRank(torus, p);
    end for;

    isotropic_mask := [];
    for i in [1..#torus`irreducibles] do
        Append(
            ~isotropic_mask,
            forall{p : p in set_of_places | LocalRank(torus`irreducibles[i], p) eq 0});
    end for;

    isotropic := SubFromMask(torus, isotropic_mask);
    anisotropic := SubFromMask(torus, [not el : el in isotropic_mask]);

    return isotropic, anisotropic;
end intrinsic;

intrinsic SIsotropicDecomposition(torus::AlgTor, set_of_places::SeqEnum[ExtReElt]) -> AlgTor, AlgTor
    {Trivial Overload for the case where places are given in FldRat}

    require AbsoluteDegree(torus`baseField) eq 1 :
        "Can only specify places in Q, if the basefield is Q";
    set_of_places := [Decomposition(torus`baseField, el)[1][1] : el in set_of_places];
    return SIsotropicDecomposition(torus, set_of_places);
end intrinsic;

intrinsic SIsotropicDecomposition(torus::AlgTor, set_of_places::SeqEnum[RngIntElt]) -> AlgTor, AlgTor
    {Trivial Overload for the case where places are given in FldRat}

    require AbsoluteDegree(torus`baseField) eq 1 :
        "Can only specify places in Q, if the basefield is Q";
    set_of_places := [Decomposition(torus`baseField, el)[1][1] : el in set_of_places];
    return SIsotropicDecomposition(torus, set_of_places);
end intrinsic;

intrinsic SIsotropicDecomposition(torus::AlgTor, set_of_places::SeqEnum[Infty]) -> AlgTor, AlgTor
    {Trivial Overload for the case where places are given in FldRat}

    require AbsoluteDegree(torus`baseField) eq 1 :
        "Can only specify places in Q, if the basefield is Q";
    set_of_places := [Decomposition(torus`baseField, el)[1][1] : el in set_of_places];
    return SIsotropicDecomposition(torus, set_of_places);
end intrinsic;

intrinsic SubFromMask(torus::AlgTor, mask::<>) -> AlgTor
    {given a torus and a list of false/true for each irreducible
    return the subtorus specified by taking only the irreds with true in the mask}

    mask := [el: el in mask];
    return SubFromMask(torus, mask);
end intrinsic;

intrinsic SubFromMask(torus::AlgTor, mask::[BoolElt]) -> AlgTor
    {given a torus and a list of false/true for each irreducible
    return the subtorus specified by taking only the irreds with true in the mask}
    indices := [i : i in [1..#mask] | mask[i]];

    if &or mask eq false then
        res := AlgebraicTorus(torus`baseField);
        // we want to realize res in the same algebra as torus
        if IsRealized(torus) then
            res`realizingElements := [Universe(torus`realizingElements) |];
            res`centralIdempotents := [Universe(torus`centralIdempotents) |];
        end if;
    else
        irreds := [torus`irreducibles[i] : i in indices];
        if IsRealized(torus) then
            realizing_elements := [torus`realizingElements[i] : i in indices];
            central_idempotents := [torus`centralIdempotents[i] : i in indices];
        else
            realizing_elements := false;
            central_idempotents := false;
        end if;

        res := AlgebraicTorus(irreds :
            realizing_elements:=realizing_elements,
            central_idempotents:=central_idempotents);

        if assigned torus`generators then
            res`generators := [torus`generators[i] : i in indices];
        end if;
    end if;

    return res;
end intrinsic;

intrinsic SubtoriAsMasks(torus::AlgTor) -> SeqEnum[AlgTor]
    {Return a SeqEnum of all the subtori.}
    return CartesianProduct([[false,true] : i in [1..#torus`irreducibles]]);
end intrinsic;
