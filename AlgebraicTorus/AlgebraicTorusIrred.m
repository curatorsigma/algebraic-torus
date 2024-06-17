// Definitions for AlgebraicTorusIrred and Bookkeeping / Wrapperfunctions for this type

import "../core/characters.m" :
    get_relative_galois_group,
    calculate_normpullback,
    coset_action_but_actually_usable,
    move_roots_finite;
import "../core/primitives.m" :
    find_smallest_prime_with_good_reduction_in_field,
    decomposition_but_works;
import "../core/generators.m":
    find_common_zero_of_characters;

declare type AlgTorIrr;
declare attributes AlgTorIrr:
    // REQUIRED (must be set by every Constructor)
    // The field K over which the Torus is defined, as an extension of Q
    baseField,
    // The field F fixed by the involution, as an extension of baseField
    fixedField,
    // The field E such that the (K-Points of the) Torus is a subgroup of E^\times
    // as an extension of fixedField
    extensionField,
    // In total, we have extensionField | fixedField | baseField
    // and Degree(extensionField, fixedField) in {1, 2}

    // The irreducible submodule of the Gal(Ehat | Q)-module
    // Q[Gal(Ehat | K) / Gal(Ehat | E)] / N* Q[Gal(Ehat | K) / Gal(Ehat | F)]
    // containing all the characters which do not vanish on this irreducible
    characterModule,
    // CharCollDat : the collateral data gathered from the calculation of characterModule
    collateralData,


    // OPTIONAL (one may never assume that these are set)
    // Associative Array Place of K or 0 -> rank at that place or global rank at K
    ranks,
    // RngIntElt
    globalRank,
    // An element of E generating this torus
    generator
;

intrinsic AlgebraicTorusIrred(
        field_tower::[FldNum],
        characterModule::ModGrp,
        collateralData::CharCollDat) -> AlgebraicTorusIrred
    {Basic Constructor for AlgebraicTorusIrred}
    baseField, fixedField, extensionField := Explode(field_tower);

    // Check that baseField is defined over Q
    require BaseRing(baseField) eq Rationals(): "baseField must be defined over Rationals()";
    // Check that fixedField | baseField
    require BaseRing(fixedField) eq baseField: "fixedField must be defined over baseField";
    // Check that either extensionField is equal to fixedField or defined over it of degree 2
    if not extensionField eq fixedField then
        // Check that extensionField | fixedField
        require BaseRing(extensionField) eq fixedField:
            "extensionField must be defined over fixedField or equal to it.";
        require Degree(extensionField, fixedField) in [1, 2] :
            "The Degree of extensionField over fixedField must be 1 or 2";
    end if;

    // Check that characterModule is Irreducible
    require #Decomposition(characterModule) eq 1: "characterModule must be irreducible";

    // Done validating. Create the new AlgebraicTorusIrred
    res := New(AlgTorIrr);
    res`baseField := baseField;
    res`fixedField := fixedField;
    res`extensionField := extensionField;

    res`characterModule := characterModule;
    res`collateralData := collateralData;

    return res;
end intrinsic;

intrinsic Dimension(torus::AlgTorIrr) -> RngIntElt
    {The Dimension of an irreducible Torus.}
    return Dimension(torus`characterModule);
end intrinsic;

intrinsic Print(torus::AlgTorIrr)
    {Print for irreducible torus.}
    printf "AlgebraicTorus defined over %o of dimension %o",
        torus`baseField, Dimension(torus);
end intrinsic;

// trivial overload
intrinsic WeilRestriction(torus::AlgTorIrr, new_base_field::FldRat) -> AlgTor
    {Overload WeilRestriction for the rational field as new base.}

    return WeilRestriction(torus, QNF());
end intrinsic;

intrinsic WeilRestriction(torus::AlgTorIrr, new_base_field::FldNum) -> AlgTor
    {Weil-Restric the torus to a smaller basefield.

    INPUTS
        AlgTorIrr torus: the torus to restrict
        FldNum new_base_field: the new baseField after restriction
    OUTPUTS
        AlgTor: the result of the restriction
    NOTES
        The Result will usually not be irreducible!}

    // input validation
    new_base_field := AbsoluteField(new_base_field);
    require new_base_field subset torus`baseField :
        "The new baseField must a subset of the old one.";

    restricted_torus := New(AlgTor);
    restricted_torus`baseField := new_base_field;

    // get the new relative galois group
    galois_group_over_new := get_relative_galois_group(
        torus`collateralData`galoisGroupOverQ,
        new_base_field, torus`extensionField,
        torus`collateralData`roots);

    if not torus`collateralData`galoisGroupOverBaseField subset galois_group_over_new then
        error "Galois group over smaller field is not a supergroup of old Galois group.";
    end if;

    // get a set of representatives for Gal(Ehat | old_base) \ Gal(Ehat | new_base)
    new_over_old_reps := DoubleCosetRepresentatives(
        galois_group_over_new,
        torus`collateralData`galoisGroupOverBaseField,
        sub<galois_group_over_new | galois_group_over_new ! 1>);

    // get the galois group over the extension field
    tmp := GSet(torus`collateralData`galoisGroupOverQ);
    galois_group_over_extension_field := Stabiliser(torus`collateralData`galoisGroupOverQ, tmp[1]);
    if not galois_group_over_extension_field subset galois_group_over_new then
        error "Galois Group over Extension field is not a subgroup of galois group over new basefield.";
    end if;

    // create the Module over the smaller basefield, without the norm-quotient
    descent, coset_action_group, _ := coset_action_but_actually_usable(
        galois_group_over_new,
        galois_group_over_extension_field);
    complete_new_module := GModule(coset_action_group, Rationals());

    complete_old_module := Domain(torus`collateralData`characterQuotientHom);
    // Ordered set of Representatives of Gal(Ehat | fixed_field) \ Gal(Ehat | old_base)
    reps_for_old_basis := GSet(Group(complete_old_module));

    list_of_generators := [complete_new_module ! 0 : j in [1..#new_over_old_reps]];

    for b in Basis(torus`characterModule) do
        // get the preimages of b
        preimage := b @@ torus`collateralData`characterQuotientHom;
        // now translate the preimage into generators in the characters for the new base field
        for i in [1..Dimension(complete_old_module)] do
            if Eltseq(preimage)[i] eq 0 then
                continue i;
            end if;
            // to apply an element in the new module, we need descent instead of
            // torus`collateralData`actionDescent
            for j in [1..#new_over_old_reps] do
                list_of_generators[j] +:= Eltseq(preimage)[i] *
                    (complete_new_module.1 *
                     descent(reps_for_old_basis[i] * new_over_old_reps[j]));
            end for;
        end for;
    end for;

    // create the new character module
    new_module_before_quotient := sub<complete_new_module | list_of_generators>;

    gset := GSet(galois_group_over_new);
    galois_group_over_extension_field := Stabiliser(galois_group_over_new, gset[1]);

    galois_group_over_fixed_field := get_relative_galois_group(
        torus`collateralData`galoisGroupOverQ,
        torus`fixedField, torus`extensionField,
        torus`collateralData`roots);

    normpullback := calculate_normpullback(
        galois_group_over_new,
        galois_group_over_fixed_field,
        galois_group_over_extension_field,
        complete_new_module);
    npb_in_new := normpullback meet new_module_before_quotient;
    new_module, char_quotient := quo<new_module_before_quotient | npb_in_new>;

    if not Dimension(new_module) eq
            AbsoluteDegree(torus`baseField) / AbsoluteDegree(new_base_field)
            * Dimension(torus`characterModule) then
        error "The Weil-Restricted Module has the wrong dimension.";
    end if;

    // the new module may be reducible. decompose it and create a new irreducible torus for each element
    irreds := Decomposition(new_module);

    // we need to fudge the collateral data a bit
    new_collateral_data := CharacterCollateralData(
        torus`collateralData`galoisGroupOverQ,
        galois_group_over_new,
        galois_group_over_extension_field,
        char_quotient,
        descent,
        torus`collateralData`roots);
    // we need to redefine the fields so that the tower is defined correctly
    _ := IsSubfield(new_base_field, torus`fixedField);
    new_fixed_field := RelativeField(new_base_field, torus`fixedField);
    _ := IsSubfield(new_fixed_field, torus`extensionField);
    new_extension_field := RelativeField(new_fixed_field, torus`extensionField);

    list_of_irreducibles := [];
    for irred_index in irreds do
        irreducible_torus := AlgebraicTorusIrred(
            [new_base_field,
             new_fixed_field,
             new_extension_field],
            irred_index,
            new_collateral_data);
        Append(~list_of_irreducibles, irreducible_torus);
    end for;

    restricted_torus`irreducibles := list_of_irreducibles;
    return restricted_torus;
end intrinsic;

intrinsic IsIsomorphic(A::AlgTorIrr, B::AlgTorIrr) -> BoolElt
    {Check whether two irreducible tori are isomorphic as Algebraic Groups.}

    // first off, the base field has to be the same
    if not IsIsomorphic(A`baseField, B`baseField) then
        return false;
    end if;

    // the charactermodules have to have the same dimension
    if not Dimension(B`characterModule) eq Dimension(A`characterModule) then
        return false;
    end if;

    // the actions have to be isomorphic
    if not IsIsomorphic(MatrixGroup(B`characterModule), MatrixGroup(A`characterModule)) then
        return false;
    end if;

    // The tori are isomorphic.
    return true;
end intrinsic;

intrinsic FieldTowersAreIsomorphic(A::AlgTorIrr, B::AlgTorIrr) -> BoolElt
    {Check whether A and B were created over the same field tower up to isomorphism.}

    if not IsIsomorphic(A`baseField, B`baseField) then
        return false;
    end if;
    if not IsIsomorphic(A`fixedField, B`fixedField) then
        return false;
    end if;
    if not IsIsomorphic(A`extensionField, B`extensionField) then
        return false;
    end if;
    return true;
end intrinsic;

intrinsic LocalRank(A::AlgTorIrr, place::Infty) -> RngIntElt
    {Redirect when the basefield is the rational field.}
    require AbsoluteDegree(A`baseField) eq 1 :
        "The place may only be given as infty when the baseField is the rationals.";

    place_in_bf := InfinitePlaces(A`baseField)[1];

    return LocalRank(A, place_in_bf);
end intrinsic;

intrinsic LocalRank(A::AlgTorIrr, place::RngIntElt) -> RngIntElt
    {Redirect when the basefield is the rational field.}
    require IsPrime(place) : "The Place must be a finite prime, Infinity or a PlcNumElt.";
    require AbsoluteDegree(A`baseField) eq 1 :
        "The place may only be given as a finite prime when the baseField is the rationals.";
    place_in_bf := Decomposition(A`baseField, place)[1][1];

    return LocalRank(A, place_in_bf);
end intrinsic;

intrinsic LocalRank(A::AlgTorIrr, place::PlcNumElt) -> RngIntElt
    {Calculate the local rank of this irreducible torus at a place.

    Redirect to LocalRank of AlgTor (see the comment there for a reasoning.)

    SIDEEFFECT:
        caches global and local rank}

    require place in Places(A`baseField) : "The place must be in Places(A`baseField)";

    // check if the result is already cached. Do not recompute it in that case
    if assigned A`ranks then
        is_cached, rank := IsDefined(A`ranks, place);
        if is_cached then
            return rank;
        end if;
    end if;
    alg_tor := AlgebraicTorus([A]);
    return LocalRank(alg_tor, place);
end intrinsic;

intrinsic GlobalRank(A::AlgTorIrr) -> RngIntElt
    {Calculate the global rank of this irreducible torus.

    This calls LocalRank at a prime internally.}
    if assigned A`globalRank then
        return A`globalRank;
    end if;

    p := find_smallest_prime_with_good_reduction_in_field(A`extensionField);
    place := Decomposition(A`baseField, p)[1][1];
    _ := LocalRank(A, place);
    assert assigned A`globalRank;

    return A`globalRank;
end intrinsic;

intrinsic _CacheRank(A::AlgTorIrr, place::PlcNumElt, rank::RngIntElt)
    {Set the Rank at the given place to rank.

    This is useful since the rank calculation happens on AlgTor, not AlgTorIrr.}

    if not assigned A`ranks then
        A`ranks := AssociativeArray(Places(A`baseField));
    end if;

    require place in Places(A`baseField) : "The place must be in Places(A`baseField)";

    // ranks are immutable. If the rank changed, an error must have occured in the calculation
    is_cached, cached_rank := IsDefined(A`ranks, place);
    if is_cached then
        require cached_rank eq rank :
            "Rank at this place is already cached with another value.";
    end if;
    A`ranks[place] := rank;
end intrinsic;

intrinsic _CacheGlobalRank(A::AlgTorIrr, rank::RngIntElt)
    {Set the global rank to rank.}
    if assigned A`globalRank and A`globalRank ne rank then
        require false : "Global rank is already cached with a different value.";
    end if;
    A`globalRank := rank;
end intrinsic;

intrinsic Hash(A::AlgTorIrr) -> RngIntElt
    {Hash for AlgTorIrr.}

    list_of_raw_info := [*
        "TYPE::AlgTorIrr",
        A`baseField,
        A`fixedField,
        A`extensionField,
        // maps do not have proper hashes. Use the characterModule itself
        A`characterModule,
        (assigned A`generator) select A`generator else "EMPTY-GENERATOR"
    *];

    return Hash(list_of_raw_info);
end intrinsic;

intrinsic 'eq'(A::AlgTorIrr, B::AlgTorIrr) -> BoolElt
    {Check two AlgTorIrr for equality.}
    return Hash(A) eq Hash(B);
end intrinsic;

/// Return true iff A has positive rank at any of the places
///
/// INPUTS
///  AlgTorIrr A
///  List or SeqEnum[PlcNumElt in Places(A`baseField)] set_of_places
/// OUTPUTS
///  BoolElt : true iff the rank of A at any of these places is positive
function _has_S_rank(A, set_of_places)
    for place in set_of_places do
        if LocalRank(A, place) gt 0 then
            return true;
        end if;
    end for;
    return false;
end function;

/// Calculate characters that have to be killed for an element of e to belong to this irreducible torus
///
/// INPUTS
///  AlgTorIrr A
///  List[ModGrp] irreds of X_S; S is a Torus containing A
/// OUTPUTS
///  List[Elements of X_E]: a basis for the characters all elements of this irreducible torus kill
///      X_E is the preimage of X_S (i.e. before taking the quotient by the normpullback)
///      E is the Algebra to which X_E is the full character space
function calculate_characters_to_kill(A, irreds)
    characters_to_kill := [];
    // first calculate the characters defined by the quotient X_E to X_S
    // (they have to be killed to be in S)
    for b in Basis(Kernel(A`collateralData`characterQuotientHom)) do
        Append(~characters_to_kill, Domain(A`collateralData`characterQuotientHom) ! b);
    end for;

    // now go over each other irreducible and add their characters
    // (if an element kills all characters of S except those belonging to A,
    //  that element lies in A)
    for irred in irreds do
        if IsIsomorphic(irred, A`characterModule) then
            continue irred;
        end if;
        for b in Basis(irred) do
            // b is in the quotient. We need a representative in the Preimage
            // because we want to talk about elements of E,
            // on which elements of X_E (not X_S) act
            char_tmp := Domain(A`collateralData`characterQuotientHom)
                ! Codomain(A`collateralData`characterQuotientHom)
                ! b;
            assert2 char_tmp in Domain(A`collateralData`characterQuotientHom);
            assert2 A`collateralData`characterQuotientHom(char_tmp) eq b;
            Append(~characters_to_kill, char_tmp);
        end for;
    end for;
    return characters_to_kill;
end function;

intrinsic _GoodGeneratorPlace(A::AlgTorIrr) -> PlcNumElt
    {Find a place in A`baseField at which the generator search will succeed.}
    // choose the smallest prime such that in A`extensionField s' defining polynomial is
    // squarefree mod prime (slightly stronger then "prime is unramified in A`extensionField")
    // where A has rank. Since completely split primes have rank, this is guaranteed to terminate.
    p := 2;
    while true do
        p := NextPrime(p);
        if not IsSquarefree(PolynomialRing(GF(p)) ! DefiningPolynomial(AbsoluteField(A`extensionField))) then
            continue;
        end if;
        for place in Decomposition(A`baseField, p) do
            if LocalRank(A, place[1]) gt 0 then
                return place[1];
            end if;
        end for;
    end while;
end intrinsic;

intrinsic ArbitraryGenerator(A::AlgTorIrr
        : set_of_places:=false) -> FldNumElt
    {Find an element of A`extensionField that lies in this irreducible
    and generates it.

    If set_of_places is given, all of the following must be true:
        - A has rank at one of the places
        - A has no A`baseField-rank
        - all of the places are unramified in NormalClosure(A´extensionField)

    If any of these conditions is not satisfied, this function panics.
    Otherwise, the returned generator will be an S-unit where S are the places
    in A`extensionField lying over set_of_places.

    If set_of_places cmpeq or is an empty List/SeqEnum, the smallest prime unramified in
    A`extensionField is chosen instead.}

    if GlobalRank(A) eq 1 then
        return A`extensionField ! 2;
    end if;

    if set_of_places cmpeq false then
        set_of_places := [_GoodGeneratorPlace(A)];
    else
        require Type(set_of_places) in [List, SeqEnum] :
            "If places are given, they must be a list or SeqEnum.";
        if #set_of_places eq 0 then
            return ArbitraryGenerator(A : set_of_places := false);
        else
            require forall{x : x in set_of_places | Type(x) eq PlcNumElt} :
                "If places are given, they must be PlcNumElt.";
            require forall{x : x in set_of_places | x in Places(A`baseField)} :
                "If places are given, they must be in Places(A`baseField).";
        end if;
    end if;
    for p in set_of_places do
        if not IsSquarefree(PolynomialRing(GF(Characteristic(ResidueClassField(p))))
            ! DefiningPolynomial(AbsoluteField(A`extensionField))) then
            A; set_of_places; p;
            require false :  "The torus' extension fields' defining polynomial must be squarefree mod all primes.";
        end if;
    end for;
    require _has_S_rank(A, set_of_places) : "The torus must have rank at the provided places.";

    irreds := Decomposition(Codomain(A`collateralData`characterQuotientHom));
    chars_to_kill := calculate_characters_to_kill(
        A,
        irreds);
    // Any common zero of these characters is in A
    // A is irreducible, so any of its elements of infinite order generates it
    generator := find_common_zero_of_characters(
        AbsoluteField(A`extensionField),
        chars_to_kill,
        set_of_places,
        A`collateralData`galoisGroupOverQ);
    return A`extensionField ! generator, set_of_places;
end intrinsic;
