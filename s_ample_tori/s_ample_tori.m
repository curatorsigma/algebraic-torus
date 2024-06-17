// The complete function calculating S-Ample tori

//////////////
// imports
import "../core/primitives.m" :
    find_isomorphism_type,
    decomposition_but_works,
    calculate_fixed_field_raw,
    direct_sum_decomposition_but_works,
    relative_field_but_does_not_segfault;

function idpots_from_relization_map(abstract_to_realization)
    // Given an isomorphism from an abstract Etale Algebra into its realization,
    // calculate the minimal nontrivial idempotents of the realization

    abstract := Domain(abstract_to_realization);

    idpots := [];
    // create the 1 in each field in abstract, then push it to realization
    for i in [1..#abstract`extensions] do
        one_in_field := abstract ! [(k eq i) select 1 else 0 : k in [1..#abstract`extensions]];
        Append(~idpots, abstract_to_realization(one_in_field));
    end for;
    return idpots;
end function;

/// Given
///  - two matrix algebras
///      - the first of which is a subalgebra of the second,
///      - both etale
///      - both involutively closed
///  - a map from full_alg into an abstract etale algebra isomorphic to it
/// 
/// Calculate
///  - A list with entries of the following format:
///      - <Subalgebra K_i of sub_alg, Subalgebra E_i of full_alg>
///  - a single Subalgebra E_0 of full_alg (the remainder)
///  - The Raw return values from DirectSumDecomposition(full_alg) (to avoid recomputation)
///  The return values are such that
///  - each K_i is isomorphic to a numberfield
///  - each K_i is a subalgebra of E_i and each E_i is minimal with this property
///  - sub_alg = sum_i K_i (direct)
///  - full_alg = E_0 + sum_i E_i (direct)
///
/// INPUTS
///  AlgMat sub_alg
///  AlgMat full_alg
/// OUTPUTS
///  SeqEnum[Tuple<AlgMat, AlgMat>]
///  AlgMat
function find_injections(sub_alg, full_alg, to_eta_alg)
    assert full_alg eq Domain(to_eta_alg);
    assert sub_alg subset full_alg;
    assert IsInvolutivelyClosed(sub_alg, full_alg);

    Ks := direct_sum_decomposition_but_works(sub_alg);

    // since we know that full_alg is the realization of Codomain(to_eta_alg),
    // we can calculate the idpots by hand and do not have to call DirectSumDecomposition
    idpots := idpots_from_relization_map(Inverse(to_eta_alg));
    Ls := [sub<full_alg | [idpots[i] * b * idpots[i] : b in Basis(full_alg)]> : i in [1..#idpots]];

    injections := [**];
    for K in Ks do
        Ls_this_K_embedds_into := [];
        for Lindex in [1..#Ls] do
            // create the smash idpot * K * idpot
            smash := sub<full_alg | [idpots[Lindex] * b * idpots[Lindex] : b in Basis(K)]>;
            // K injects into L iff the smash is nontrivial
            if Dimension(smash) gt 0 then
                Append(~Ls_this_K_embedds_into, Ls[Lindex]);
            end if;
        end for;
        Append(~injections, <K, Ls_this_K_embedds_into>);
    end for;
    assert2 sub<full_alg | [tup[1] : tup in injections]> eq sub_alg;

    // the remainder is every L that is not part of any of the injections above
    rem_basis := [];
    for L in Ls do
        for tup in injections do
            if L in tup[2] then
                continue L;
            end if;
        end for;
        rem_basis cat:= Basis(L);
    end for;
    remainder := sub<full_alg | rem_basis>;
    assert2 IsInvolutivelyClosed(remainder, full_alg);

    // add all the Ls together into one algebra
    for index in [1..#injections] do
        injections[index] := <
            injections[index][1],
            sub<full_alg | injections[index][2]>>;
    end for;
    assert2 sub<full_alg | [injections[index][2] : index in [1..#injections]] cat [remainder]> eq full_alg;

    return injections, remainder;
end function;

/// Given an AlgMat E_realized and an FldNum K and an embedding
/// to_eta_alg : E_realized -> abstract_alg into an AlgEta
/// where
///  - K embeds into each Simple summand of E_realized
///  - E_realized is etale
/// Calculate
///  - an AlgEta E over K isomorphic to E_realized
///  - the projection abstract_alg -> E
function convert_to_abstract(E_realized, K, to_eta_alg)
    assert Type(E_realized) eq AlgMat;
    assert ISA(Type(K), FldNum);

    abstract := Codomain(to_eta_alg);
    // We need the subalgebra of abstract corresponding to E_realized
    // calculate this by smashing with the corresponding idpots
    relevant_indices_in_abstract := [];
    for i in [1..#abstract`extensions] do
        one_in_field := abstract ! [(k eq i) select 1 else 0 : k in [1..#abstract`extensions]];
        idpot := Inverse(to_eta_alg)(one_in_field);
        smash := sub<E_realized | [idpot * b * idpot : b in Basis(E_realized)]>;
        if Dimension(smash) gt 0 then
            Append(~relevant_indices_in_abstract, i);
        end if;
    end for;

    // ceate the sub of abstract_alg using only the relevant fields
    E_abstract, E_abstract_to_abstract := SubFromMask(abstract, [
        i in relevant_indices_in_abstract
        : i in [1..#abstract`extensions]]);

    // redefine over K
    redefined, E_abstract_to_redefined := RedefineOverNewField(E_abstract, K);
    abstract_to_redefined := Inverse(E_abstract_to_abstract) * E_abstract_to_redefined;
    redefined_to_realized := Inverse(abstract_to_redefined) * Inverse(to_eta_alg);

    inv_on_redefined := map<redefined -> redefined |
        x :-> Inverse(redefined_to_realized)(_Conjugate(redefined_to_realized(x)))>;
    redefined := InvolutiveAlgebra(redefined, inv_on_redefined);

    assert2 Domain(abstract_to_redefined) eq abstract;
    assert2 Codomain(abstract_to_redefined) eq redefined;

    return redefined, abstract_to_redefined;
end function;

/// Helper for ranks_of_centraliser.
/// Given the injection data and the full algebra,
/// sort the subalgebras in each injection based on whether
/// the involution restrics on them or swaps them
function find_inv_types(injections, full_alg)
    // All the pairs of indices in injections for which the
    // involution swaps the two elements of the pair
    swap_Ks := [];
    // All the indices in injections for which the involution restricts
    // on the smaller field
    restrict_Ks := [];
    // now go over all the injections one-by-one. Fill the swap and restrict types
    for index in [1..#injections] do
        // skip swap-type pairs we already know. Their structure is irrelevant for the ranks
        if exists{pair : pair in swap_Ks | index in pair} then
            continue index;
        end if;
        K_realized := injections[index][1];
        // fill swap_Ks and restrict_Ks
        is_restrict := true;
        for b in Basis(K_realized) do
            conj := _Conjugate(full_alg ! b);
            if not conj in K_realized then
                for j in [1..#injections] do
                    if conj in injections[j][1] then
                        Append(~swap_Ks, [index, j]);
                        is_restrict := false;
                        break b;
                    end if;
                end for;
            end if;
        end for;
        if is_restrict then
            Append(~restrict_Ks, index);
        else
            continue index;
        end if;
    end for;

    if GetAssertions() ge 2 then
        for index in [1..#injections] do
            assert index in restrict_Ks xor exists{pair : pair in swap_Ks | index in pair};
        end for;
        for pair in swap_Ks do
            K1 := injections[pair[1]][1];
            K2 := injections[pair[2]][1];
            assert sub<K1 | [K1 ! _Conjugate(full_alg ! b) : b in Basis(K2)]> eq K1;
        end for;
    end if;

    return restrict_Ks, swap_Ks;
end function;

/// Helper function for ranks_of_centraliser
function add_local_ranks_of_su(abstract_alg, twist, full_to_abstract_alg, set_of_places, ranks)

    // push the twist into abstract_alg
    res_twist := full_to_abstract_alg(twist);
    // calculate the involution given by the twisted trace form
    realization, generic_of_realization, abstract_to_realization := 
        InvolutiveLeftRegularEmbedding(abstract_alg, res_twist);

    K := BaseRing(realization);

    for place in set_of_places do
        ranks[place] +:= LocalRankOfSU(generic_of_realization, place);
    end for;
    return ranks;
end function;

/// GIVEN
///  - AlgMats sub_alg < full_alg
///  - a finite set of places of BaseRing(sub_alg) =: F
///  - an isomorphism to_eta_alg : full_alg -> A into an AlgEta
///  - an eps-hermitian twist in A, which was used to define the involution on full_alg
/// WHERE
///  - full_alg is involutive
///  - sub_alg is a sub-*-alg of full_alg (involutively closed)
/// CALCULATE
///  - for each place p in set_of_places:
///      - rk_p C_SU(full_alg)(sub_alg) {which is considered an F-Scheme}
/// OUTPUTS
///  Assoc {PlcNumElt of F -> RngIntElt (the rank)}
function ranks_of_centraliser(sub_alg, full_alg, twist,
                              set_of_places, to_eta_alg)
    // this is the result array we will fill later
    ranks := AssociativeArray();
    F := BaseRing(sub_alg);
    for p in set_of_places do
        if Type(p) eq PlcNumElt then
            assert NumberField(p) eq F;
        else
            assert Type(F) eq FldRat;
        end if;

        ranks[p] := 0;
    end for;

    // Find injection data (which subfield of sub_alg injects where in full_alg)
    //      - This is calculated in the AlgMat full_alg
    injections, remainder := find_injections(sub_alg, full_alg, to_eta_alg);
    restrict_Ks, swap_Ks := find_inv_types(injections, full_alg);

    // Calculate the rank from restrict types
    for index in restrict_Ks do
        K_realized := injections[index][1];
        E_realized := injections[index][2];

        // get E_realized as an abstract Etale Algebra
        // and the map
        // full_to_E : Codomain(to_eta_alg) -> E_as_abstract_K_algebra
        K := find_isomorphism_type(K_realized);
        E_as_abstract_K_algebra, full_to_E := convert_to_abstract(E_realized, K, to_eta_alg);

        // M_m(K) is involutive with the twisted trace form. We need to find the involution and
        // rk_p(SU_m(K, inv)), which this helper does.
        ranks := add_local_ranks_of_su(
            E_as_abstract_K_algebra,
            twist,
            full_to_E,
            set_of_places, ranks);
    end for;

    // Calculate the rank from swap-type Ks
    // The SU here is SU(M_m(K) + M_m(K), swap) = GL(M_m(K)).
    // Use [JS, Prop 5.1.8] (rk_p(GL_m(K)) = m * #{Places of K over p}).
    for index in swap_Ks do
        K_realized := injections[index][1];
        dimension := Integers() ! (
            &+[Dimension(el) : el in injections[index][2]]
            / Dimension(K_realized));
        K := find_isomorphism_type(K_realized);
        for p in set_of_places do
            ranks[p] +:= dimension * #decomposition_but_works(K, p);
        end for;
    end for;

    // Calculate the rank from the noninjected part (remainder)
    // This is equivalent to an injection <baseField, remainder>
    remainder_abstract, full_to_remainder := convert_to_abstract(
        remainder, BaseField(Codomain(to_eta_alg)), to_eta_alg);

    ranks := add_local_ranks_of_su(
        remainder_abstract,
        twist,
        full_to_remainder,
        set_of_places, ranks);

    // Calculate the rank of the central torus
    // use [JS, Prop 5.1.7]:
    //  rk_p(Z)) = sum_{restrict case} #{places in K_i^τ that split in K_i}
    // where K_i^τ is the fixed field of K_i under τ, and we only consider fields of the restrict case
    for index in restrict_Ks do
        K_realized := injections[index][1];
        K, real_to_abstract := find_isomorphism_type(K_realized);
        // find the fixed field - the involution restricts to K_realized.
        fixed_field := calculate_fixed_field_raw(
            K,
            real_to_abstract(
                _Conjugate(full_alg !
                    Inverse(real_to_abstract)(K.1))));
        fixed_field := relative_field_but_does_not_segfault(
            F, fixed_field);
        K_rel := relative_field_but_does_not_segfault(fixed_field, K);
        for p in set_of_places do
            // count the places of F which split in K
            res := #[p_fixed_field
                : p_fixed_field in decomposition_but_works(fixed_field, p)
                | #decomposition_but_works(K_rel, p_fixed_field[1]) gt 1];
            ranks[p] +:= res;
        end for;
    end for;

    return ranks;
end function;

/// Given
/// - An involutive Etale Algebra alg
/// - an eps-hermitian element of alg
/// - a finite set of places of alg`baseField
/// Calculate
/// - all the S-ample subtori of SU(alg), embedded with the twisted Traceform into M_n(alg`baseField)
function find_S_ample_subtori(alg, twist, set_of_places)

    // if the algebra is over QNF and set_of_places are over FldRat, move them
    if AbsoluteDegree(BaseRing(alg)) eq 1 and Type(BaseRing(alg)) eq FldNum then
        set_of_places := [
            Type(p) ne PlcNumElt
                select Decomposition(BaseRing(alg), p)[1][1]
                else p
                : p in set_of_places];
    end if;

    // now we realize the algebra into matrices with the twisted traceform
    // as_matrices will have the involution given by the traceform attached to it
    as_matrices, generic_as_matrices, alg_to_as_matrices := InvolutiveLeftRegularEmbedding(
        alg, twist : update_realization:=true);

    // Create SU(alg) with its associated involution
    maximal_torus := AlgebraicTorus(alg);
    assert3 FullRealizingAlgebra(maximal_torus) subset as_matrices;

    // we do not care about S-compact subtori. Throw them away
    // all tori which are S-ample are subtori of anisotropic by definition.
    isotropic, anisotropic := SIsotropicDecomposition(maximal_torus, set_of_places);

    // by condition (1), no irred of isotropic can be in an S-ample torus: they have no rank at S
    // by condition (3), no irred of anisotropic can *miss* from an S-ample torus:
    //  that irred would still be in the centraliser, but have positive S-rank, which is forbidden.
    // Therefore, anisotropic is the only subtorus of maximal_torus that can be S-ample.

    // Now check the centralisers:
    sub_alg := FullRealizingAlgebra(anisotropic);
    roc := ranks_of_centraliser(
        sub_alg,
        as_matrices,
        twist,
        set_of_places,
        Inverse(alg_to_as_matrices));

    for p in set_of_places do
        printf "Place %o: centraliser-rank = %o, torus-rank = %o\n",
            p, roc[p], LocalRank(anisotropic, p);
        assert roc[p] ge LocalRank(anisotropic, p);
    end for;
    if forall{p : p in set_of_places | roc[p] eq LocalRank(anisotropic, p)} then
        return [anisotropic];
    end if;

    return [];
end function;
