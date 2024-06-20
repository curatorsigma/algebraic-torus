// functions to calculate character modules and their ranks

///////////////
// Calculate Character-Module and local ranks

// imports
import "constants.m" :
    PRECISION,
    PRECISION_LOW,
    PRECISION_TO_CONSIDER_FOR_EQUALITY_CHECK_IN_CC;
import "primitives.m":
    flatten_list,
    find_smallest_prime_with_good_reduction_in_field,
    cast_from_FldPad_to_RngLocA,
    decomposition_but_works,
    decomposition_group_but_works,
    fix_but_works,
    relative_field_but_does_not_segfault,
    corresponding_irred;

/// Like CosetAction, but GSet(Group(X)) returns the RightTransversal
function coset_action_but_actually_usable(G, H)
    ts, transversal_map := RightTransversal(G, H);
    Y := GSet(G, ts, map<CartesianProduct(ts, G) -> ts | x :-> transversal_map(x[1] * x[2])>);
    return Action(G, Y);
end function;

/// Return true iff a == 0 up to precision errors
/// (works for RngLocAElt and FldComElt)
function _zero_to_precision(a)
    if a eq 0 then
        return true;
    end if;

    if Type(a) in [FldComElt, FldReElt] then
        return Floor(Modulus(a) * 10^(PRECISION_TO_CONSIDER_FOR_EQUALITY_CHECK_IN_CC)) eq 0;
    end if;

    if Type(a) eq RngLocAElt then
        return RelativePrecision(a) eq 0;
    end if;

    if ISA(Type(a), FldNumElt) then
        return a eq 0;
    end if;

    "This type is not known:";
    Type(a);
    assert false;
end function;

/// Return true iff g fixes base_field
///
/// INPUTS
///  GrpPermElt g: Element of the galois group of E^
///  FldNum E
///  SeqEnum[RngLocAElt] roots_in_new: the roots of DefiningPolynomial(E) in a local splitting field
///      Note that they are not(!) data`Roots (they are RngPadElt, but we need them as RngLocAElt)
///  FldNum E_abs: an absolute version of E
///  FldNum base_field smaller than E
/// OUPUTS
///  BoolElt true iff g fixes base_field
///      The calculation is based on whether g acts trivially on
///      Basis(base_field) after localization
function _element_fixes_subfield(
        g, E, roots_in_new, E_abs,
        base_field)
    assert #roots_in_new ge 1;
    EF_loc_split := Parent(roots_in_new[1]);

    difference_cast := map<E_abs -> EF_loc_split | map_x :-> &+[
        ((roots_in_new[1^g])^(j-1) - (roots_in_new[1])^(j-1))
        * Eltseq(map_x)[j] : j in [1..Degree(E_abs)]]>;

    for x in Basis(AbsoluteField(base_field)) do
        if not _zero_to_precision(difference_cast(E_abs ! x)) then
            return false;
        end if;
    end for;
    return true;
end function;

/// Calculate the relative galois group when its order is known
///
/// INPUTS
///  GrpPerm G: Gal(extension_field^|Q)
///  data: galoisData from the calculation of G
///  FldNum base_field: the field we want Gal(extension_field^|base_field) of
///  FldNum extension_field
///  SeqEnum[RngLocAElt] roots_in_new: the roots of DefiningPolynomial(E) in a local splitting field
///      Note that they are not(!) data`Roots (they are RngPadElt, but we need them as RngLocAElt)
///  RngIntElt known_order: The order the relative galois group has
///  GrpPerm G: a subgroup of G that is known to be a subgroup of the result
/// OUTPUTS
///  GrpPerm Gal(extension_field^|base_field)
function _rel_gal_group_degree_known(
            G, base_field, extension_field, roots_in_new,
            known_order, known_subgroup)
    // iterate over the subgroups of correct order
    subgroup_classes_of_correct_order := Subgroups(
        G : OrderEqual:=known_order);

    for i in [1..#subgroup_classes_of_correct_order] do
        for candidate in Conjugates(G, subgroup_classes_of_correct_order[i]`subgroup) do
            // skip groups which do not contain the known subgroup
            if not known_subgroup subset candidate then
                continue candidate;
            end if;

            // test explicitly whether candidate
            // fixes BF (i.e. whether it is the correct conjugate)
            for g in Generators(candidate) do
                if not _element_fixes_subfield(
                        g, extension_field, roots_in_new,
                        AbsoluteField(extension_field),
                        base_field) then
                    continue candidate;
                end if;
            end for;

            assert3 candidate subset G;
            assert3 known_subgroup subset candidate;
            assert3 #candidate eq known_order;
            return candidate;
        end for;
    end for;
    "\nERROR. debug output:";
    G; base_field; extension_field; roots_in_new; known_order; known_subgroup;
    "Could not find the relative Galois Group.";
    assert false;
end function;

/// Given the GaloisGroup over Q, calculate it over base_field
///
/// INPUTS
///  GrpPerm G: GaloisGroup over Q
///  FldNum base_field: a subfield of the Field, G is the Galois Group of
///  FldNum extension_field: The field E, such that G is the Galois Group of NormalClosure(E)|Q
///  SeqEnum[RngLocAElt] roots_in_new: the roots of DefiningPolynomial(E) in a local splitting field
///      Note that they are not(!) data`Roots (they are RngPadElt, but we need them as RngLocAElt)
///  GrpPerm KnownSubgroup:=sub<G | G ! 1> :
///      If it is known that this group is a subgroup of the result, we can speed up the calculation
/// OUTPUTS
///  Subgroup of G that corresponds to Gal(... | base_field)
function get_relative_galois_group(
        G, base_field, extension_field, roots_in_new:
        KnownSubgroup:=sub<G | G ! 1>)
    // short circuit if possible
    if Degree(base_field, Rationals()) eq 1 then
        return G;
    end if;

    // If BF is normal over Q, we know the correct order of the final group we need
    // but calculating normality is only efficient when BF is absolute
    if IsAbsoluteField(base_field) and IsNormal(base_field) then
        known_order := Integers() ! (#G / Degree(base_field));
        _, tmp := Quotrem(known_order, #KnownSubgroup);
        // the subgroup order must divide the result order
        assert tmp eq 0;
        return _rel_gal_group_degree_known(
            G, base_field, extension_field, roots_in_new,
            known_order,
            KnownSubgroup);
    end if;

    // prepare some information required for checking the fix
    EF_loc_split := Parent(roots_in_new[1]);

    // recast E | base_field, then absolutize E
    E := relative_field_but_does_not_segfault(base_field, extension_field);
    E_abs := AbsoluteField(E);

    // first check that the known subgroup is actually contained in the result
    for g in Generators(KnownSubgroup) do
        fixes := _element_fixes_subfield(
            g, E, roots_in_new,
            E_abs, base_field);
        if not fixes then
            "Error: The supplied known subgroup can not be correct.";
            KnownSubgroup; G; base_field;
            assert false;
        end if;
    end for;

    // start a bottom-up search
    current := KnownSubgroup;
    while true do
        current_changed_flag := false;
        for super in MinimalOvergroups(G, current) do
            // select an arbitrary element of super \ current
            gen := [g : g in super | not g in current][1];
            fixes := _element_fixes_subfield(
                gen, E, roots_in_new, E_abs, base_field);
            // if a generator fixes base_field, super fixes it
            // because super is minimal over current (i.e. super = <current, gen>)
            if fixes then
                // make a step up and continue
                current := super;
                current_changed_flag := true;
                break;
            end if;
        end for;
        if not current_changed_flag then
            // No supergroup of current fixes base_field.
            // Since MinimalOvergroups returns an exhaustive list, we are done.
            break;
        end if;
    end while;
    return current;
end function;

/// Calculate the full image of the Normpullback
///
/// INPUTS
///  GrpPerm galois_group_over_base_field
///  GrpPerm galois_group_over_fixed_field
///  GrpPerm galois_group_over_extension_field
///  ModGrp X_EF : the characters of EF over BF
///  Map[ModGrp, ModGrp]: the action of galois_group_over_base_field on X_EF
/// OUTPUTS
///  ModGrp the normpullback as a submodule of X_EF
function calculate_normpullback(
        galois_group_over_base_field,
        galois_group_over_fixed_field,
        galois_group_over_extension_field,
        X_EF)
    // NOTES
    //  We have the Norm
    //      N : EF -> FF
    //  The norm induces
    //      N*: X_FF -> X_EF; defined by N*(σ) (e) = σ(N(e)) (σ in X_FF, e in EF)
    //  We need to find the full image of N*, which is what this function calculates.
    //  We have
    //      X_EF = Q[Gal(EFhat|EF)\Gal(EFhat|BF)] and
    //      X_FF = Q[Gal(EFhat|FF)\Gal(EFhat|BF)]
    //  We calculate the normpullback on the Basis
    //      Γ := Gal(EFhat|FF)\Gal(EFhat|BF).
    //  Let σ be a representative of such a class (an element of Gal(EFhat|BF))
    //  Let ρ be the unique nontrivial Element of Gal(EF|FF). Then
    //      N*(Gal(EFhat|FF) * σ) = Gal(EFhat|EF) * 1 * σ + Gal(EFhat|EF) * ρ * σ
    //          (written with the action from the right)

    //  given Gal(EFhat|EF) * 1 * σ, the unique other left-coset
    //  wrt Gal(EFhat|EF) that has the same Gal(EFhat|FF)-left-coset is
    //  Gal(EFhat|EF) * ρ * σ
    //      (it is such a coset and [EF:FF] = 2, so exactly two Gal(EFhat|EF)
    //       cosets have the same Gal(EFhat|FF)-cosets)

    // When we now group the elements of Δ := Gal(EFhat|EF)\Gal(EFhat|BF)
    // into pairs according to their Gal(EFhat|FF)-cosets,
    // this yields a partition of Δ and for any element in Γ,
    // its image under N* is the formal sum over one of the pairs in Δ

    //  We can thus calculate the image of N* in the following way:
    //  - partition Δ as above
    //  - This yields all the formal sums 1 * σ + ρ * σ that can occur as
    //    N*(x) for some x \in Γ
    //  - The Span of all those sums is Im(N*)
    //      (recall that Γ is a Q-Basis of X_FF)

    coset_reps_to_EF := GSet(Group(X_EF));
    // the groups of two cosets to EF, as described above
    groups := [];
    for coset_index in [1..#coset_reps_to_EF] do
        // skip cosets that are already sorted into some group
        for g in groups do
            if coset_index in g then
                continue coset_index;
            end if;
        end for;

        for other_index in [1..#coset_reps_to_EF] do
            if coset_index eq other_index then
                continue other_index;
            end if;
            if galois_group_over_fixed_field * coset_reps_to_EF[coset_index]
                    eq galois_group_over_fixed_field * coset_reps_to_EF[other_index] then
                // coset_index and other_index have the same coset to Gal(EFhat|FF)
                // (i.e. they have the same image under φ)
                Append(~groups, [coset_index, other_index]);
                continue coset_index;
            end if;
        end for;
    end for;
    // each coset should have occured exactly once
    assert2 forall{x : x in [1..#coset_reps_to_EF] | exists(t){g : g in groups | x in g}};

    normpullback := sub<X_EF | [X_EF ! [(j in group) select 1 else 0 : j in [1..Dimension(X_EF)]]
                                : group in groups]>;
    // The dimension of the normpullback should be dim(X_EF) / [EF:FF]
    assert3 #galois_group_over_fixed_field * Dimension(normpullback) eq
            #galois_group_over_extension_field * Dimension(X_EF);
    return normpullback;
end function;

/// helper functions for the finite place cases of ranks_of_irreds_at_prime
///  (this is essentially a type cast and does no interesting mathematics)
///
/// GIVEN
///  - the p-Adic roots in a FldPad isomorphic to L completed at some (unknown) extension of place
///  - FldNums L | K
///  - a place of K which is finite
/// CALCULATE
///  - an RngLocA isomorphic to Universe(roots[1]), defined over Completion(K, place)
///  - the roots in that field
/// NOTES
///  - L is only used for error-checking
function move_roots_finite(roots, K, L, place)
    L_loc_split_fldpad := Parent(roots[1]);
    assert Prime(L_loc_split_fldpad) eq Characteristic(ResidueClassField(place));
    // GaloisGroup should give the roots as RngPad
    assert2 ISA(Type(L_loc_split_fldpad), RngPad);
    precision := Minimum([Precision(r) : r in roots]);
    // L_loc_split is now the same tower as L_loc_split_fldpad but RngLocA
    L_loc_split, pad_to_tower := cast_from_FldPad_to_RngLocA(
        L_loc_split_fldpad : MinPrecision:=precision);
    // L_loc_split is now absolute over Q_p
    L_loc_split, tower_to_new := AbsoluteField(L_loc_split);
    pad_to_new := pad_to_tower * tower_to_new;
    assert2 AbsoluteDegree(L_loc_split) eq Degree(L_loc_split);

    // find K_p as a completion of K at place
    K_p, K_to_Kp := Completion(K, place);
    assert2 ISA(Type(K_p), FldPad);
    K_p`DefaultPrecision := Precision(L_loc_split);
    f_K_p := DefiningPolynomial(K_p);
    if AbsoluteDegree(L_loc_split) eq 1 then
        K_p := BaseRing(L_loc_split);
        roots_in_new := [pad_to_new(r) : r in roots];
    else
        // convert K_p to a subfield of L_loc_split
        rts := Roots(f_K_p, L_loc_split);
        K_p, iota := sub<L_loc_split | [el[1] : el in rts]>;
        // RelativeField prints internally and I cannot change the code, so redirect-blackhole instead
        SetOutputFile("/dev/null");
        L_loc_split, _, new_to_relative_over_BFp := RelativeField(L_loc_split, iota);
        UnsetOutputFile();
        // cast roots into the new field
        roots_in_new := [new_to_relative_over_BFp(pad_to_new(r)) : r in roots];
    end if;

    assert2 forall{x : x in roots_in_new | x in L_loc_split};
    assert2 forall{x
                   : x in roots_in_new
                   | RelativePrecision(Evaluate(DefiningPolynomial(
                        AbsoluteField(L)), x)) eq 0};
    return L_loc_split, roots_in_new;
end function;

/// helper function for ranks_of_irreds_at_prime
///
/// GIVEN
///  - A GrpPerm G, galois group of L|K
///  - An RngLocA L_loc, local splitting field of L
///  - the roots of L's defining polynomial in L_loc
/// CALCULATE
///  - the Decompositiongroup of an (unknown) place P of L such that L_loc = L_P
function local_galois_group_finite(G, L_loc, roots)
    // find the local Galois Group
    // Gal_Lloc_Kp == Gal(L_loc | K_p), which is the local group we want
    Gal_Lloc_Kp_abstract, map := AutomorphismGroup(L_loc);
    assert2 #Gal_Lloc_Kp_abstract le #G;
    generators_in_g := [];
    for h in Generators(Gal_Lloc_Kp_abstract) do
        h_as_permutation := [0 : i in [1..#roots]];
        for i in [1..#roots] do
            diff_vals := [];
            for j in [1..#roots] do
                difference := map(h)(roots[i]) - roots[j];
                Append(~diff_vals, Valuation(difference));
                // printf "difference at %o, %o:\n%o\nmit Valuation %o\n\n", i, j, difference, Valuation(difference), "Minimal";
            end for;
            max_valauation, min_index := Maximum(diff_vals);
            if max_valauation eq 0 then
                diff_vals; Gal_Lloc_Kp_abstract; h; i;
                error "The image of a root is not a root while trying to find local galois group.";
            end if;
            h_as_permutation[i] := min_index;
        end for;
        Append(~generators_in_g, h_as_permutation);
    end for;
    assert3 forall{x : x in generators_in_g | IsCoercible(G, x)};
    Gal_Lloc_Kp := sub<G | generators_in_g>;

    assert #Gal_Lloc_Kp_abstract eq #Gal_Lloc_Kp;
    assert IsIsomorphic(Gal_Lloc_Kp_abstract, Gal_Lloc_Kp);
    return Gal_Lloc_Kp;
end function;


/// Get the local galois group as an abstract GrpPerm
function _abstract_local_galois_group(
        base_field, fixed_field, extension_field,
        place)
    p := Characteristic(ResidueClassField(place));

    // we try to find the local galois group in G by figuring out the
    // correct conjugacy class of groups to use
    Z_p := pAdicField(p, 40);
    EFp_over_Zp_rngpad := SplittingField(
        PolynomialRing(Integers()) !
            DefiningPolynomial(AbsoluteField(extension_field)),
        pAdicRing(p, 40));
    gal_EFp_over_Zp, abstract_to_auts := AutomorphismGroup(EFp_over_Zp_rngpad);
    EFp_over_Zp_rngloca, pad_to_loca := cast_from_FldPad_to_RngLocA(
        EFp_over_Zp_rngpad);
    BFp_in_loca := sub<EFp_over_Zp_rngloca | [x[1] : x in Roots(
        PolynomialRing(Z_p) ! DefiningPolynomial(base_field),
        EFp_over_Zp_rngloca)]>;
    // start a bottom-up search
    current := sub<gal_EFp_over_Zp | gal_EFp_over_Zp ! 1>;
    while true do
        current_changed_flag := false;
        // go through the MinimalOvergroups of current
        for super in MinimalOvergroups(gal_EFp_over_Zp, current) do
            // select an arbitrary element of super \ current
            gen := [g : g in super | not g in current][1];
            gen_fixes_base_field := forall{
                i : i in [1..Degree(BFp_in_loca)]
                // move the basis element to RngPad, apply gen, move back
                | IsWeaklyZero(
                    (Inverse(pad_to_loca) * abstract_to_auts(gen) * pad_to_loca)
                        (BFp_in_loca.1^i) - BFp_in_loca.1^i)};
            // if a generator fixes base_field, super fixes it
            // because super is minimal over current (i.e. super = <current, gen>)
            if gen_fixes_base_field then
                current := super;
                current_changed_flag := true;
                break super;
            end if;
        end for;
        if not current_changed_flag then
            // no supergroup of current fixes base_field
            // since MinimalOvergroups returns an exhaustive list, we are done.
            gal_EFp_over_BFp := current;
            break;
        end if;
    end while;

    // we now know gal_EFp_over_BFp acting on the roots in a local
    // splitting field, but we need it acting on the roots of
    // DefiningPolynomial(AbsoluteField(extension_field)) in a localization
    // so that we can compare the action on these roots to the action
    // of the global galois group on the same roots in a global splitting field
    roots_in_EFp_over_BFp := [x[1] : x in Roots(
        DefiningPolynomial(AbsoluteField(extension_field)),
        EFp_over_Zp_rngpad)];
    gens_acting_on_roots := [];
    for g in Generators(gal_EFp_over_BFp) do
        images_under_gen := [];
        for i in [1..#roots_in_EFp_over_BFp] do
            image := abstract_to_auts(g)(roots_in_EFp_over_BFp[i]);
            diff_vals := [];
            for j in [1..#roots_in_EFp_over_BFp] do
                difference := image - roots_in_EFp_over_BFp[j];
                Append(~diff_vals, Valuation(difference));
            end for;
            max_valauation, min_index := Maximum(diff_vals);
            if max_valauation eq 0 then
                diff_vals; i; image; roots_in_EFp_over_BFp; gal_EFp_over_BFp;
                error "The image of a root is not a root while trying to find local galois group.";
            end if;
            Append(~images_under_gen, min_index);
        end for;
        Append(~gens_acting_on_roots, images_under_gen);
    end for;
    gal_EFp_over_BFp_on_roots := sub<
        SymmetricGroup(#gens_acting_on_roots[1])
        | gens_acting_on_roots>;

    return gal_EFp_over_BFp_on_roots;
end function;

/// GIVEN
///     - a GrpPerm grp with a Map into the Auts of some field
///     - a SeqEnum[FldElt] of roots on which grp acts
/// CALCULATE
///     - the corresponding GrpPerm acting naturally on those roots
function aut_group_to_group_on_roots(grp, grp_to_auts, roots)
    gens_acting_on_roots := [];
    for gen in Generators(grp) do
        Append(~gens_acting_on_roots, [Index(roots, grp_to_auts(gen)(r))  : r in roots]);
    end for;
    group_on_roots := sub<SymmetricGroup(#roots) | gens_acting_on_roots>;
    assert IsIsomorphic(grp, group_on_roots);
    return group_on_roots;
end function;

/// Calculate the local Galois Group
/// Gal(EFhat_P | BF_place) for some P over place
///
/// INPUTS
///  FldNum base_field (BF): The field over which the Torus is to be defined
///  FldNum fixed_field (FF): The field fixed by the involution
///  FldNum extension_field (EF): The larger field (extension of degree 2)
///  PlcNumElt place: Place in BF to calculate local group at; this place is ramified in EFhat
///  G, roots, data: output of GaloisGroup at an unramified prime
///      (this may or may not be the prime below place)
/// OUTPUTS
///  BoolElt true iff a new galois group had to be calculated
///  GrpPerm Gal(EFhat_P | BF_p)
///     is guaranteed to be subset G iff the first return is false
///     is guaranteed to be subset Gal(EFhat | Q) iff the first return is true
///  GrpPerm Gal(EFhat | Q) when the first return is true, 0 else
///  GrpPerm Gal(EFhat | BF) when the first return is true, 0 else
///  GrpPerm Gal(EFhat | FF) when the first return is true, 0 else
///  GrpPerm Gal(EFhat | EF) when the first return is true, 0 else
///     all the latter four returns are guaranteed to be subset Gal(EFhat | Q) iff the first return is true
///  roots, on which Gal(EFhat | Q) acts naturally iff the first return is true, 0 else
/// NOTES
///  If the second output is false, the third and fourth are undefined and have no meaning.
function local_galois_group_ram(
        base_field, fixed_field, extension_field,
        place,
        G, roots, data)
    // we are in the following case:
    // place has bad reduction in NormalClosure(EF) and G was calculated over
    // another prime (with good reduction): data`Prime

    // get the local galois group - this is an abstract group and we will now
    // try to identify it as a subgroup of G
    gal_EFp_over_BFp_on_roots := _abstract_local_galois_group(
        base_field, fixed_field, extension_field, place);

    // Try to find the local group as a subgroup of the global group
    // first: get only the subgroups of correct order
    subgroup_classes_of_correct_order := Subgroups(
        G : OrderEqual:=#gal_EFp_over_BFp_on_roots);
    assert #subgroup_classes_of_correct_order ge 1;
    if #subgroup_classes_of_correct_order eq 1 then
        return false, subgroup_classes_of_correct_order[1]`subgroup, 0, 0, 0, 0, 0;
    end if;

    // second: get only the subgroups with correct S_n conjugacy class
    subgroup_classes_sn_conjugate := [];
    for class in subgroup_classes_of_correct_order do
        if IsConjugate(Generic(class`subgroup), class`subgroup, gal_EFp_over_BFp_on_roots) then
            Append(~subgroup_classes_sn_conjugate, class);
        end if;
    end for;
    assert #subgroup_classes_sn_conjugate ge 1;
    if #subgroup_classes_sn_conjugate eq 1 then
        return false, subgroup_classes_sn_conjugate[1]`subgroup, 0, 0, 0, 0, 0;
    end if;

    // there are to many subgroup classes that could fit, so we have to actually
    // calculate a splitting field and get the local group from that
    Ehat_abs := AbsoluteField(GaloisSplittingField(
        DefiningPolynomial(AbsoluteField(extension_field))
        : Galois:=<G, roots, data>));
    Ehat := relative_field_but_does_not_segfault(base_field, Ehat_abs);
    places_in_Ehat := decomposition_but_works(Ehat, place);

    // Third: We can ignore subgroup classes whose number of G-conjugates
    // is not equal to the number of places
    subgroup_classes_acceptable_conjugacy_length := [];
    for class in subgroup_classes_sn_conjugate do
        if class`length le #places_in_Ehat then
            Append(~subgroup_classes_acceptable_conjugacy_length, class);
        end if;
    end for;
    assert #subgroup_classes_acceptable_conjugacy_length ge 1;
    if #subgroup_classes_acceptable_conjugacy_length eq 1 then
        return false, subgroup_classes_acceptable_conjugacy_length[1]`subgroup, 0, 0, 0, 0, 0;
    end if;

    // select a random place in Ehat and calculate its decomposition group
    place_in_Ehat := places_in_Ehat[1][1];
    // this is now a subgroup of AutomorphismGroup(Ehat)
    decomposition_group := decomposition_group_but_works(place_in_Ehat);

    // We need to guarantee that the galois groups are subgroups of each other
    // to do this, we can act with everything on the absolute global roots of E in Ehat_abs
    auts_Ehat, _, grp_to_auts := AutomorphismGroup(Ehat_abs);
    roots := [x[1] : x in Roots(DefiningPolynomial(AbsoluteField(extension_field)), Ehat_abs)];

    Gal_EFhat_QQ := aut_group_to_group_on_roots(auts_Ehat, grp_to_auts, roots);    
    assert decomposition_group subset auts_Ehat;
    Gal_EFloc_BF_p := aut_group_to_group_on_roots(decomposition_group, grp_to_auts, roots);

    Gal_EFhat_EF := get_relative_galois_group(
        Gal_EFhat_QQ, extension_field, extension_field, roots);
    Gal_EFhat_FF := get_relative_galois_group(
        Gal_EFhat_QQ, fixed_field, extension_field, roots);
    Gal_EFhat_BF := get_relative_galois_group(
        Gal_EFhat_QQ, base_field, extension_field, roots);

    assert Gal_EFloc_BF_p subset Gal_EFhat_BF;
    assert Gal_EFhat_BF subset Gal_EFhat_QQ;
    assert Gal_EFhat_FF subset Gal_EFhat_BF;
    assert Gal_EFhat_EF subset Gal_EFhat_FF;
    return true, Gal_EFloc_BF_p, Gal_EFhat_QQ, Gal_EFhat_BF, Gal_EFhat_FF, Gal_EFhat_EF, roots;
end function;

/// place needs to be the one used to calculate G, roots, data
function get_all_relative_galois_groups(
        base_field, fixed_field, extension_field,
        G, roots, data, place)
    // move the roots to RngLocA
    EF_loc_split, roots_in_new := move_roots_finite(
        roots, base_field, extension_field, place);

    // find Gal(EFhat | EF)
    Gal_EFhat_EF := Stabiliser(G, 1);
    assert3 Gal_EFhat_EF eq get_relative_galois_group(
        G,
        extension_field,
        extension_field, roots_in_new);
    // and Gal(EFhat | FF)
    Gal_EFhat_FF := get_relative_galois_group(
        G,
        fixed_field,
        extension_field, roots_in_new:
        KnownSubgroup:=Gal_EFhat_EF);
    // and Gal(EFhat | BF)
    Gal_EFhat_BF := get_relative_galois_group(
        G,
        base_field,
        extension_field, roots_in_new:
        KnownSubgroup:=Gal_EFhat_FF);
    return Gal_EFhat_EF, Gal_EFhat_FF, Gal_EFhat_BF, EF_loc_split, roots_in_new;
end function;

/// Get all groups when place is unramified
function get_all_galois_groups_unram(
        base_field, fixed_field, extension_field, place : Prec:=PRECISION)
    p := Characteristic(ResidueClassField(place));
    // Get the global GaloisGroup over Q
    Gal_EFhat_QQ, roots, data := GaloisGroup(
        AbsoluteField(extension_field) : Prime:=p, Prec:=Prec);
    assert data`Prime eq p;

    assert2 forall{x : x in roots
                     | RelativePrecision(Evaluate(DefiningPolynomial(
                        AbsoluteField(extension_field)), x)) eq 0};
    assert2 #roots eq #Set(roots);

    Gal_EFhat_EF, Gal_EFhat_FF, Gal_EFhat_BF, EF_loc_split, roots_in_new :=
        get_all_relative_galois_groups(
            base_field, fixed_field, extension_field,
            Gal_EFhat_QQ, roots, data, place);

    // We need the local galois group for the local ranks
    Gal_EFloc_BF_p := local_galois_group_finite(
        Gal_EFhat_BF, EF_loc_split, roots_in_new);

    assert Gal_EFhat_BF subset Gal_EFhat_QQ;
    assert Gal_EFloc_BF_p subset Gal_EFhat_BF;
    assert Gal_EFhat_FF subset Gal_EFhat_BF;
    assert Gal_EFhat_EF subset Gal_EFhat_FF;
    return Gal_EFhat_QQ, Gal_EFhat_EF, Gal_EFhat_FF, Gal_EFhat_BF, Gal_EFloc_BF_p, roots_in_new;
end function;

/// Calculate
///  GrpPerm Gal(EFhat | Q) =: G
///  Gal(EFhat | EF) as a subgroup of G
///  Gal(EFhat | FF) as a subgroup of G
///  Gal(EFhat | BF) as a subgroup of G
///  Gal(EFhat_p | BF_p) as a subgroup of G
function get_all_galois_groups(base_field, fixed_field, extension_field, place
        : Prec:=PRECISION)
    p := Characteristic(ResidueClassField(place));

    // if p has good reduction, this is easy - short circuit.
    if IsSquarefree(PolynomialRing(GF(p)) !
            DefiningPolynomial(AbsoluteField(extension_field))) then
        return get_all_galois_groups_unram(
            base_field, fixed_field, extension_field, place : Prec:=Prec);
    end if;

    // we now know that p is ramified
    p_unram := find_smallest_prime_with_good_reduction_in_field(
        AbsoluteField(extension_field));
    place_unram := decomposition_but_works(base_field, p_unram)[1][1];
    // Get the global GaloisGroup over Q - at an unramified prime
    G, roots, data := GaloisGroup(
        AbsoluteField(extension_field) : Prime:=p_unram, Prec:=Prec);

    assert2 forall{x : x in roots
                     | RelativePrecision(Evaluate(DefiningPolynomial(
                        AbsoluteField(extension_field)), x)) eq 0};
    assert2 #roots eq #Set(roots);
    // We need the local galois group for the local ranks
    supergroup_recalc_done, Gal_EFloc_BF_p, Gal_EFhat_QQ, Gal_EFhat_BF, Gal_EFhat_FF, Gal_EFhat_EF, roots_with_natural_action :=
        local_galois_group_ram(
            base_field, fixed_field, extension_field,
            place,
            // the original group calculation
            G, roots, data
        );
    if not supergroup_recalc_done then
        Gal_EFhat_EF, Gal_EFhat_FF, Gal_EFhat_BF, EF_loc_split, roots_with_natural_action :=
            get_all_relative_galois_groups(
                base_field, fixed_field, extension_field,
                G, roots, data, place_unram);
        Gal_EFhat_QQ := G;
    end if;

    assert Gal_EFhat_BF subset Gal_EFhat_QQ;
    assert Gal_EFloc_BF_p subset Gal_EFhat_BF;
    assert Gal_EFhat_FF subset Gal_EFhat_BF;
    assert Gal_EFhat_EF subset Gal_EFhat_FF;
    return Gal_EFhat_QQ, Gal_EFhat_EF, Gal_EFhat_FF, Gal_EFhat_BF, Gal_EFloc_BF_p, roots_with_natural_action;
end function;

/// Calculate the global and local ranks of L|K at p and the global irreds of the charactermodule
///
/// INPUTS
///  FldNum base_field: The field over which the Torus is to be defined
///  FldNum fixed_field: The field fixed by the involution
///  FldNum extension_field: The larger field (extension of degree 2)
///  Finite Place of base_field p:
///      Place to use for calculation (ranks are calculated at this Place)
/// OUTPUTS
///  List[ModGrp] irreducibles
///  List[RngIntElt] global ranks of the irreds
///  List[RngIntElt] p-Ranks of the irreds
///  Tuple<GrpPerm Gal(ΕFhat|Q),
///        GrpPerm Gal(EFhat|BF),
///        Map[ModGrp, ModGrp] the QuotientMap of which the image is the complete charactermodule,
///        GaloisData,
///        Map: Map to act on the charactermodule with the GaloisGroup,
///        GrpPerm Gal(EFhat | EF)>
/// NOTES
///  The Rational Points of the Normtorus (and thus the chracters) are G-isomorphic to EF^x
/// SHORTHANDS
///  base_field == BF
///  fixed_field == FF
///  extension_field == EF
function ranks_of_irreds_at_prime_ext(base_field, fixed_field, extension_field, place
                                      : Prec:=PRECISION)

    Gal_EFhat_QQ, Gal_EFhat_EF, Gal_EFhat_FF, Gal_EFhat_BF, Gal_EFloc_BF_p, roots :=
        get_all_galois_groups(base_field, fixed_field, extension_field, place : Prec:=Prec);
    descent, coset_action_group, _ := coset_action_but_actually_usable(
        Gal_EFhat_BF,
        Gal_EFhat_EF);
    X_EF := GModule(coset_action_group, Rationals());
    assert Dimension(X_EF) eq Degree(extension_field, base_field);

    normpullback := calculate_normpullback(
        Gal_EFhat_BF,
        Gal_EFhat_FF,
        Gal_EFhat_EF,
        X_EF);

    X_S, char_quotient := quo<X_EF | normpullback>;
    assert Dimension(X_S) eq Degree(fixed_field, base_field);
    assert2 Dimension(fix_but_works(X_S)) eq 0;
    // These are Q-irreducibles
    irreds := Decomposition(X_S);

    q_ranks := [];
    p_ranks := [];
    for irred_index in [1..#irreds] do
        // each irred has rank 1 precicely if it is trivial, 0 otherwise
        Append(~q_ranks, Dimension(Fix(irreds[irred_index])));
        Append(~p_ranks, &+[Dimension(Fix(el)) :
                            el in Decomposition(Restriction(irreds[irred_index],
                                                descent(Gal_EFloc_BF_p)))]);
    end for;


    // print("TODO DEBUG");
    // e1moved := _ApplyCharacter(X_EF.1, extension_field.1, CharacterCollateralData(
    //     Gal_EFhat_QQ, Gal_EFhat_BF, Gal_EFhat_EF, char_quotient, descent, roots));
    // print(e1moved);

    return irreds, q_ranks, p_ranks, CharacterCollateralData(
        Gal_EFhat_QQ, Gal_EFhat_BF, Gal_EFhat_EF, char_quotient, descent, roots);
end function;


/// Calculate the global and local ranks of L|K at p and the global irreds of the charactermodule
///
/// INPUTS
///  FldNum base_field: The field over which the Torus is to be defined
///  FldNum fixed_field: The field fixed by the involution
///  Finite Place of base_field p:
///      Place to use for calculation (ranks are calculated at this Place)
/// OUTPUTS
///  List[ModGrp] irreducibles
///  List[RngIntElt] global ranks of the irreds
///  List[RngIntElt] p-Ranks of the irreds
///  Tuple<GrpPerm Gal(FFhat|Q),
///        GrpPerm Gal(FFhat|BF),
///        Map[ModGrp, ModGrp] the QuotientMap of which the image is the complete charactermodule,
///        GaloisData,
///        Map: Map to act on the charactermodule with the GaloisGroup,
///        GrpPerm Gal(FFhat | FF)>
/// NOTES
///  The Rational Points of the Normtorus (and thus the chracters) are G-isomorphic to FF^x
/// SHORTHANDS
///  base_field == BF
///  fixed_field == FF
function ranks_of_irreds_at_prime_swap(base_field, fixed_field, place : Prec:=PRECISION)
    p := Characteristic(ResidueClassField(place));

    Gal_FFhat_QQ, Gal_FFhat_FF, Gal_FFhat_FF, Gal_FFhat_BF, Gal_FFloc_BF_p, roots :=
        get_all_galois_groups(base_field, fixed_field, fixed_field, place : Prec:=Prec);
    descent, coset_action_group, _ := coset_action_but_actually_usable(
        Gal_FFhat_BF,
        Gal_FFhat_FF);
    X_FF := GModule(coset_action_group, Rationals());
    assert Dimension(X_FF) eq Degree(fixed_field, base_field);

    descent, coset_action_group, _ := coset_action_but_actually_usable(
        Gal_FFhat_BF, Gal_FFhat_FF);
    X_FF := GModule(coset_action_group, Rationals());
    irreds := Decomposition(X_FF);

    q_ranks := [];
    p_ranks := [];
    for irred_index in [1..#irreds] do
        // each irred has rank 1 precicely if it is trivial, 0 otherwise
        Append(~q_ranks, Dimension(Fix(irreds[irred_index])));
        Append(~p_ranks, &+[Dimension(Fix(el)) :
                            el in Decomposition(Restriction(irreds[irred_index],
                                                            descent(Gal_FFloc_BF_p)))]);
    end for;

    _, char_quotient := quo<X_FF | 0>;
    return irreds, q_ranks, p_ranks, CharacterCollateralData(
        Gal_FFhat_QQ, Gal_FFhat_BF, Gal_FFhat_FF, char_quotient, descent, roots);
end function;

/// GIVEN
///  - a place (Infinity or PlcNumElt and IsInfinite(...))
///  - complex(or real) roots
///  - a galois group G relative to NumberField(place) (or Rationals())
/// CALCULATE
///  - the decompositiongroup of P | place as a subgroup of G
/// WHERE
///  - P is the (unknown) PlcNumElt over place such that roots live in its completion
function local_auts_at_infinite_place(place, roots, G : Prec:=PRECISION)
    // check if the local splitting field is totally real.
    // In this case, there are no nontrivial auts.
    all_roots_are_real := true;
    for r in roots do
        if Imaginary(r) ge 10^(-Prec + 1) then
            all_roots_are_real := false;
            break r;
        end if;
    end for;
    // check if there are nontrivial local auts
    local_auts_are_trivial := false;
    if Type(place) eq PlcNumElt then
        if IsComplex(place) then
            // if BF_p is already complex, the local
            // extension EF_P | BF_p can not have nontrivial auts
            local_auts_are_trivial := true;
        else
            // BF_p is Real. All auts are trivial iff EF_loc is also real
            local_auts_are_trivial := all_roots_are_real;
        end if;
    else
        // BF_p is Real. All auts are trivial iff EF_loc is also real
        local_auts_are_trivial := all_roots_are_real;
    end if;

    if local_auts_are_trivial then
        return sub<G | G ! 1>;
    end if;

    // we now know that there are nontrivial auts
    // find the local auts as a subgroup of G
    images_of_generators_of_h_in_g := [];
    h_as_permutation := [0 : i in [1..#roots]];
    for i in [1..#roots] do
        for j in [1..#roots] do
            // the nontrivial local aut is always complex conjugation
            if Abs(Conjugate(roots[i]) - roots[j]) lt 10^(-PRECISION_LOW) then
                // this is a hit. i |-> j under the image of h in G
                h_as_permutation[i] := j;
                continue i;
            end if;
        end for;
    end for;
    Append(~images_of_generators_of_h_in_g, h_as_permutation);
    res := sub<G | images_of_generators_of_h_in_g>;

    if not #res eq 2 then
        assert "Local auts are nontrivial, but the local group is." cmpeq 0;
    end if;

    return res;
end function;

/// Calculate the global and local ranks of L|K at an infinite place
/// and the global irreds of the charactermodule
///
/// INPUTS
///  FldNum|FldRat base_field: The field over which the Torus is to be defined
///  FldNum fixed_field: The field fixed by the involution
///  FldNum extension_field: The larger field (extension of degree 2)
///                         or the same as fixed_field (swap-type involution)
///  Infinite Place of base_field place: The infinite place to calculate rank at
/// OUTPUTS
///  List[ModGrp] irreducibles
///  List[RngIntElt] global ranks of the irreds
///  List[RngIntElt] oo-Ranks of the irreds
///  Tuple<GrpPerm Gal(ΕFhat|Q),
///        GrpPerm Gal(EFhat|BF),
///        Map[ModGrp, ModGrp] the QuotientMap of which the image is the complete charactermodule,
///        GaloisData,
///        Map: Map to act on the charactermodule with the GaloisGroup,
///        GrpPerm Gal(EFhat | EF)>
/// SHORTHANDS
///  base_field == BF
///  fixed_field == FF
///  extension_field == EF
function ranks_of_irreds_at_infinity_ext(base_field, fixed_field, extension_field, place : Prec:=PRECISION)
    assert ISA(Type(extension_field), FldNum);
    assert ISA(Type(fixed_field), FldNum);
    assert BaseField(extension_field) eq fixed_field;
    assert ISA(Type(base_field), FldNum) or Type(base_field) eq FldRat;
    assert BaseField(fixed_field) eq base_field;
    assert (Type(place) eq PlcNumElt and IsInfinite(place)) or place cmpeq Infinity();

    // Get the global GaloisGroup
    G, roots, data := GaloisGroup(
        AbsoluteField(extension_field) : Type:="Complex", Prec:=Prec);

    // Quotient by the Normpullback
    // First find Gal(EFhat|EF) in G. It is defined by stabilising the first root
    // (up to isomorphism due to different ordering of the roots)
    Gal_EFhat_EF := Stabiliser(G, 1);
    assert3 Gal_EFhat_EF eq get_relative_galois_group(
        G, extension_field, extension_field, roots);
    // now find Gal_EFhat_FF.
    Gal_EFhat_FF := get_relative_galois_group(
        G, fixed_field,
        extension_field, roots :
        KnownSubgroup:=Gal_EFhat_EF);
    // Get Gal(EFhat | BF)
    Gal_EFhat_BF := get_relative_galois_group(
        G, base_field, extension_field, roots :
        KnownSubgroup:=Gal_EFhat_FF);
    // local splitting field of EF over Q
    EF_loc_split := Parent(roots[1]);
    assert2 Type(EF_loc_split) in [FldRe, FldCom];
    // the local galois group
    Gal_EFloc_BF_p := local_auts_at_infinite_place(
        place, roots, Gal_EFhat_BF : Prec:=Prec);

    // The final Character group we want is then
    // Q[Gal(EFhat|BF) / Gal(EFhat|EF)] / Q[phi^-1 Gal(EFhat|BF) / Gal(EFhat|FF)]
    // under the 2:1 Map
    // φ : Gal(EFhat|BF)/Gal(EFhat|EF) ->> Gal(EFhat|BF) / Gal(EFhat|FF)
    // (NB: phi is the normpullback written in cosets of Gal instead of roots)
    descent, coset_action_group, _ := coset_action_but_actually_usable(
        Gal_EFhat_BF, Gal_EFhat_EF);
    X_EF := GModule(coset_action_group, Rationals());
    assert Dimension(X_EF) eq Degree(extension_field, base_field);
    normpullback := calculate_normpullback(
        Gal_EFhat_BF,
        Gal_EFhat_FF,
        Gal_EFhat_EF,
        X_EF);
    X_S, char_quotient := quo<X_EF | normpullback>;
    assert Dimension(X_S) eq Degree(fixed_field, base_field);
    irreds := Decomposition(X_S);

    // Calculate ranks
    q_ranks := [];
    p_ranks := [];
    for irred_index in [1..#irreds] do
        // each irred has rank 1 precicely if it is trivial, 0 otherwise
        Append(~q_ranks, Dimension(Fix(irreds[irred_index])));
        Append(~p_ranks, &+[Dimension(Fix(el)) :
                            el in Decomposition(Restriction(irreds[irred_index],
                                                descent(Gal_EFloc_BF_p)))]);
    end for;

    return irreds, q_ranks, p_ranks, CharacterCollateralData(
        G, Gal_EFhat_BF, Gal_EFhat_EF, char_quotient, descent, roots);
end function;

/// Calculate the global and local ranks of L|K at an infinite place
/// and the global irreds of the charactermodule
///
/// INPUTS
///  FldNum base_field: The field over which the Torus is to be defined
///  FldNum fixed_field: The field fixed by the involution
///  Infinite Place of base_field place: The infinite place to calculate rank at
/// OUTPUTS
///  List[ModGrp] irreducibles
///  List[RngIntElt] global ranks of the irreds
///  List[RngIntElt] oo-Ranks of the irreds
///  Tuple<GrpPerm Gal(FFhat|Q),
///        GrpPerm Gal(FFhat|BF),
///        Map[ModGrp, ModGrp] the QuotientMap of which the image is the complete charactermodule,
///        GaloisData,
///        Map: Map to act on the charactermodule with the GaloisGroup,
///        GrpPerm Gal(FFhat | FF)>
/// SHORTHANDS
///  base_field == BF
///  fixed_field == FF
function ranks_of_irreds_at_infinity_swap(base_field, fixed_field, place : Prec:=PRECISION)
    // Get the global GaloisGroup
    G, roots, data := GaloisGroup(
        AbsoluteField(fixed_field) : Type:="Complex", Prec:=Prec);
    // local splitting field of FF over Q
    FF_loc_split := Parent(roots[1]);
    assert2 Type(FF_loc_split) in [FldRe, FldCom];

    // Get Gal(FFhat | BF)
    Gal_FFhat_BF := get_relative_galois_group(
        G, base_field, fixed_field, roots);

    Gal_FFloc_BF_p := local_auts_at_infinite_place(
        place, roots, Gal_FFhat_BF : Prec:=Prec);

    gset := GSet(Gal_FFhat_BF);
    Gal_FFhat_FF := Stabiliser(Gal_FFhat_BF, gset[1]);

    descent, coset_action_group, _ := coset_action_but_actually_usable(Gal_FFhat_BF, Gal_FFhat_FF);
    X_FF := GModule(coset_action_group, Rationals());
    irreds := Decomposition(X_FF);

    // Calculate ranks
    q_ranks := [];
    p_ranks := [];
    for irred_index in [1..#irreds] do
        // each irred has rank 1 precicely if it is trivial, 0 otherwise
        Append(~q_ranks, Dimension(Fix(irreds[irred_index])));
        Append(~p_ranks, &+[Dimension(Fix(el)) :
                            el in Decomposition(Restriction(irreds[irred_index],
                                                descent(Gal_FFloc_BF_p)))]);
    end for;

    _, char_quotient := quo<X_FF | 0>;
    return irreds, q_ranks, p_ranks, CharacterCollateralData(
        G, Gal_FFhat_BF, Gal_FFhat_FF, char_quotient, descent, roots);
end function;

function ranks_of_irreds_at_place(base_field, fixed_field, extension_field, place : Prec:=PRECISION)
    place_is_infinite := not Type(place) eq RngIntElt and (place cmpeq Infinity() or IsInfinite(place));
    extension_is_swap_case := AbsoluteDegree(extension_field) eq AbsoluteDegree(fixed_field);
    if extension_is_swap_case then
        if place_is_infinite then
            irreds, q_ranks, p_ranks, col_dat := ranks_of_irreds_at_infinity_swap(
                base_field, fixed_field, place : Prec:=Prec);
        else
            irreds, q_ranks, p_ranks, col_dat := ranks_of_irreds_at_prime_swap(
                base_field, fixed_field, place : Prec:=Prec);
        end if;
    else
        if place_is_infinite then
            irreds, q_ranks, p_ranks, col_dat := ranks_of_irreds_at_infinity_ext(
                base_field, fixed_field, extension_field, place : Prec:=Prec);
        else
            irreds, q_ranks, p_ranks, col_dat := ranks_of_irreds_at_prime_ext(
                base_field, fixed_field, extension_field, place : Prec:=Prec);
        end if;
    end if;

    // sanity check the outputs
    if GetAssertions() lt 2 then
        return irreds, q_ranks, p_ranks, col_dat;
    end if;

    if extension_is_swap_case then
        assert &+q_ranks eq 1;
        assert &+p_ranks le Degree(fixed_field, base_field);
        dec := decomposition_but_works(fixed_field, place);
        assert &+p_ranks eq #dec;
    else
        assert &+q_ranks eq 0;
        assert &+p_ranks le Degree(extension_field, base_field) - 1;
        dec_to_FF := decomposition_but_works(fixed_field, place);
        if not &+p_ranks eq #[
            p : p in dec_to_FF
              | #decomposition_but_works(extension_field, p[1]) ge 2] then
            base_field; fixed_field; extension_field; irreds;
            error "p ranks are not equal to the number of places in F split in E.";
        end if;
    end if;

    return irreds, q_ranks, p_ranks, col_dat;
end function;

/// Calculate the irreducibles of the Normtorus and their ranks
///
/// INPUTS
///  FldNum base_field: The field over which the Torus is to be defined
///  FldNum fixed_field: The field fixed by the involution
///  FldNum extension_field: The larger field (extension of degree 2)
///                         or the same as fixed_field (swap-type involution)
///  List[Place of base_field]: places to calculate ranks at
/// OUTPUTS
///  List[ModGrp] irreducibles
///  List[AssociativeArray[RngIntElt] -> RngIntElt]: The ranks at each place
///      The list contains one entry per irred returned in irreds
///      Each Array has as entries: 0 - the global rank
///                                 i - the rank at the i-th element of set_of_places
///  Tuple<GrpPerm Gal(Lhat|Q),
///        GrpPerm Gal(Lhat|base_field),
///        Map[ModGrp, ModGrp] the QuotientMap of which the image is the complete charactermodule,
///        GaloisData,
///        Map: Map to act on the charactermodule with the GaloisGroup>
function ranks_of_irreds(base_field, fixed_field, extension_field, set_of_places : Prec:=PRECISION)
    if not Degree(extension_field, fixed_field) in [1, 2] then
        error "extension_field must be a degree 1 or 2 extension of fixed_field.";
    end if;
    if Degree(extension_field, fixed_field) eq 2 then
        if not BaseField(extension_field) eq fixed_field then
            error "extension_field must be defined over fixed_field.";
        end if;
    end if;
    if not BaseField(fixed_field) eq base_field then
        error "fixed_field must be defined over base_field.";
    end if;

    if base_field eq Rationals() then
        for place in set_of_places do
            if place cmpeq Infinity() or Type(place) eq RngIntElt then
                continue place;
            end if;
            if not IsPrime(place) then
                error "Places in Q must be given as finite primes or Infinity()";
            end if;
        end for;
    else
        for place in set_of_places do
            if not Type(place) eq PlcNumElt then
                error "Places in a numberfield must be given as PlcNumElt";
            end if;
        end for;
    end if;


    ranks := [];
    // make one calculation for the first place
    first_place := set_of_places[1];
    irreds, q_ranks, first_place_ranks, collateral_data := ranks_of_irreds_at_place(
        base_field, fixed_field, extension_field, first_place : Prec:=Prec);
    for irred_index in [1..#irreds] do
        Append(~ranks, AssociativeArray());
        ranks[irred_index][0] := q_ranks[irred_index];
        ranks[irred_index][1] := first_place_ranks[irred_index];
    end for;

    // now make the calculations for the other places
    for place_index in [2..#set_of_places] do
        p := set_of_places[place_index];
        new_irreds, _, p_ranks, new_col_dat := ranks_of_irreds_at_place(
            base_field, fixed_field, extension_field, p : Prec:=Prec);
        rank_already_applied_on_these_irreds := [];
        for new_irred_index in [1..#new_irreds] do
            has_corresponding_irred, old_irred_index := corresponding_irred(
                new_irreds[new_irred_index], new_col_dat,
                irreds, collateral_data);
            assert has_corresponding_irred;
            ranks[old_irred_index][place_index] := p_ranks[new_irred_index];
            Append(~rank_already_applied_on_these_irreds, old_irred_index);
        end for;
    end for;

    return irreds, ranks, collateral_data;
end function;
