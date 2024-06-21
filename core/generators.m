// functions for calculating abstract generators of irreducible tori
// note that these generators are indepentend of the realization of a torus
// and given only as Elements of the Numberfield the torus is associated to

// imports
import "constants.m" :
    PRECISION, PRECISION_LOW;
import "characters.m" :
    ranks_of_irreds_at_prime;
import "primitives.m":
    left_reg_with_integral_basis,
    cut_precision_to_n,
    mtrx_cut_precision_to_n,
    fldreelt_to_fldratelt,
    mtrx_fldreelt_to_fldratelt_truncated_at,
    fldreelt_to_fldratelt_truncated_at,
    relative_field_but_does_not_segfault;

// How many Decimal places should we forcibly ignore in the Minkowsky space?
// The calcualtion of the log-valuations has some rounding in the last decimals,
// which we forcibly remove with this constant
FORCED_PRECISION_LOSS := 3;

/// Check if g and h permute cpl_roots in the same way modulo complex conjugation
///
/// INPUTS
///  GrpPermElt g
///  GrpPermElt h
///  List[FldCplElt] roots that g and h act naturally on
/// OUTPUTS
///  BoolElt (true if the permutations g and h only differ in complex conjugation)
function is_complex_conjugate(g, h, cpl_roots)
    for i in [1..#cpl_roots] do
        c1 := cpl_roots[i^g];
        c2 := cpl_roots[i^h];
        if not c1 eq c2 and not c1 eq Conjugate(c2) then
            return false;
        end if;
    end for;
    return true;
end function;

/// Check if g and h permute roots in the same way modulo Gal(Q_pbar | Q_p)
///
/// INPUTS
///  GrpPermElt g
///  GrpPermElt h
///  List[List[RngIntElt]]: roots grouped by conjugacy (same MinPol), given by their index
///  RngIntElt num_of_roots : total number of roots
/// OUTPUTS
///  BoolElt (true if the permutations g and h only differ in Gal(Q_pbar | Q_p)-conjugation)
function is_conjugate(g, h, root_groups, num_of_roots)
    for i in [1..num_of_roots] do
        r1 := i^g;
        r2 := i^h;
        for group in root_groups do
            if r1 in group and not r2 in group then
                return false;
            end if;
        end for;
    end for;
    return true;
end function;

/// Calculate the infinite valuations of Ehat
///
/// INPUTS
///  GrpPerm G: Gal(Ehat | Q) as abstract group
///  FldNum E: the number field E
/// OUTPUTS
///  Tuple<SeqEnum[the elements of G defining infinite valuations],
///        SeqEnum[Roots of DefiningPolynomial(E) in C as acted on by G]>
/// NOTES
///  I do not know if it is possible to guarantee that we only find inequivalent valuations
///  We can only guarantee that we find at least one representative for each
///  class of inequivalent valuations; but we may return more then one.
function calculate_infinite_valuations(G, E)
    G_c, roots_c, data_c := GaloisGroup(DefiningPolynomial(AbsoluteField(E)):
                                        Type:="Complex",
                                        Prec:=PRECISION);

    check, c_to_p := IsIsomorphic(G_c, G);
    if not check then
        _ := ["Two GaloisGroup calculations returned different groups.", <1>];
    end if;

    infinite_valuations := [];
    for g in G do
        // check if there is already another element of infinite_valuations related to g
        for h in infinite_valuations do
            if is_complex_conjugate(g, h, roots_c) then
                continue g;
            end if;
        end for;
        Append(~infinite_valuations, g);
    end for;

    groups_are_conjugate, res := IsConjugate(Generic(G), G, G_c);
    if not groups_are_conjugate then
        error "Two GaloisGroups of the same field are not conjugate in S_n";
    end if;

    return infinite_valuations, [roots_c[i^res] : i in [1..#roots_c]];
end function;

/// Calculate representatives in G of the finite valuations of Ehat over prime
///
/// INPUTS
///  GrpPerm G: Gal(Ehat | Q) as abstract group
///  FldNum E: the number field E
///  RngIntElt prime: prime to do calculations over
/// OUTPUTS
///  Tuple<the elements of G defining finite valuations (all pairwise inequivalent),
///        Roots of DefiningPolynomial(E) in some local splitting field as acted on by G>
/// ASSUMPTIONS
///  prime must have good reduction in E, i.e.
///  IsSquarefree(PolynomialRing(GF(prime)) ! DefiningPolynomial(AbsoluteField(E))) MUST hold.
/// NOTES
///  Ehat|Q is normal, so Gal(Ehat|Q) acts transitively on
///  the places of Ehat|Q.
///  We do not need to know the valuations, only represent them with elements of G.
///  We choose one place (which is the first in the result list).
///      Call it P_1
///  We then calculate all other finite valuations, which are determined by an element of G
///  via P' = g * P_1. The list contains id_G and all the g calculated as representatives
///
///  Because of transitivity, it is also irrelevant which place is designated
///  P_1. We implicitly choose the one whose localization is the Universe
///  of the roots we got when calculating G
function calculate_finite_valuations(G, E, prime)
    assert IsSquarefree(PolynomialRing(GF(prime)) ! DefiningPolynomial(AbsoluteField(E)));
    G_prime, roots_prime, data_prime := GaloisGroup(DefiningPolynomial(AbsoluteField(E)):
                                                    Prime:=prime);

    // This function requires the GaloisGroup to be calculated over the correct prime.
    // If DefiningPolynomial(E) is not squarefree mod prime,
    //      this does not happen and the resulting state is unrecoverable.
    assert prime eq data_prime`Prime;

    check, prime_to_p := IsIsomorphic(G_prime, G);
    if not check then
        error "Two GaloisGroup calculations returned different groups.";
    end if;

    min_precision := Precision(Parent(roots_prime[1]));
    // the polynomial defining E|Q, but as an element of Q_p[X]
    f := Polynomial(pAdicField(prime, min_precision),
                    [Integers() ! el
                     : el in Eltseq(DefiningPolynomial(AbsoluteField(E)))]);

    // Group the roots of f into classes with the same minimal polynomial
    // (note that f is irreducible in Z[X] but not in Z_p[X]).
    fact, _ := Factorization(f);
    assert #fact eq #Decomposition(E, prime);
    root_groups := [];
    for factor_index in [1..#fact] do
        Append(~root_groups, []);

        g := Polynomial([Parent(roots_prime[1]) ! el : el in Eltseq(fact[factor_index][1])]);
        for root_index in [1..#roots_prime] do
            if Valuation(Evaluate(g, roots_prime[root_index])) eq Precision(roots_prime[1]) then
                Append(~root_groups[factor_index], root_index);
            end if;
        end for;
    end for;

    finite_valuations := [];
    for g in G do
        // check if there is already another element of finite_valuations related to g
        for h in finite_valuations do
            if is_conjugate(g, h, root_groups, #roots_prime) then
                continue g;
            end if;
        end for;
        Append(~finite_valuations, g);
    end for;

    // Sort the local roots to have the same ordering as that used by G
    groups_are_conjugate, res := IsConjugate(Generic(G), G, G_prime);
    if not groups_are_conjugate then
        error "Two GaloisGroups of the same field are not conjugate in S_n";
    end if;
    return finite_valuations, [roots_prime[i^res] : i in [1..#roots_prime]];
end function;

/// Calculate the S-Minkowski Embedding at infinite places of character(xi)
///
/// INPUTS
///  FldNumElt xi in E
///  ModGrpElt character: character in X_E to apply before the embedding
///  Grp G Galois-Group of E (Gal(Ehat | Q))
///  Tuple<List[GrpElt], List[FldCplElt]>: infinite valuations and complex roots
/// OUTPUTS
///  List[sum_{sigma in character-definition} a_sigma log|sigma(xi)|_v : v in Infinite Places of Ehat]
/// ASSUMPTIONS
///  Parent(character) eq GModule(G) {so that character can be reduced to a formal sum of roots, which are themselves the GSet of G}
function s_minkowski_embedding_at_infinite_places(
        xi, character, G, valuation_data
        : precision:=PRECISION_LOW,
        Ehat:=false,
        col_dat:=false)
    infinite_valuations, cpl_roots := Explode(valuation_data);
    print("new infinite embedding");
    print("cpl_roots");
    print(cpl_roots);

    // the empty list to fill with the correct embedding data
    embedding := [RationalField() ! 0 : r in [1..#infinite_valuations]];
    eltseq_char := Eltseq(character);
    // these are the cosets of Gal(Ehat | base_field) defining the charactermodule
    cosets := GSet(Group(Parent(character)));

    // precalculate the possible infinite valuations; we will
    // select the correct entry based on sigma without recomputation
    possible_log_vals := [];
    for i in [1..#cpl_roots] do
        // TODO remove:
        // this is the image of xi, when E is embedded into CC via the i-th root
        // problem: the places of Ehat correspond to (pairs) of complex roots of f_Ehat in Ehat
        // and not to (pairs) of complex roots of f_E in Ehat, which is what we calculate here
        // end TODO
        at_ith_root := &+[cpl_roots[i]^(j - 1) * Eltseq(xi)[j] : j in [1..Degree(Parent(xi))]];
        Append(~possible_log_vals,
               fldreelt_to_fldratelt_truncated_at(
                    Log(AbsoluteValue(at_ith_root)),
                    precision));
    end for;

    for i in [1..Dimension(Parent(character))] do
        if eltseq_char[i] eq 0 then
            continue i;
        end if;

        // sigma is an element of G which is a representative of the coset
        // corresponding to the i-th basis element of Parent(character)
        sigma := cosets[i];
        print(cosets[i]);

        log_vals := [];
        for tau in infinite_valuations do
            Append(~log_vals, possible_log_vals[1^(sigma * tau)]);
        end for;

        for place_index in [1..#log_vals] do
            embedding[place_index] +:= eltseq_char[i] * log_vals[place_index];
        end for;
    end for;
    for x in embedding do
        assert Truncate(x * 10^precision) eq x * 10^precision;
    end for;


    // TODO DEBUG
    // calculate the embedding from places in Ehat as well and see how they differ
    places := InfinitePlaces(Ehat);
    inf_emb_man := [];
    for p in places do
        // berechne v_p(char(xi))
        char_at_xi := _ApplyCharacter(character, xi, col_dat);
        assert char_at_xi in Ehat;
        Append(~inf_emb_man, Valuation(char_at_xi, p));
    end for;

    // We need to map the InfinitePlaces(Ehat) to these elements



    // print("automatic without Ehat");
    // print([Universe(inf_emb_man) ! x : x in embedding]);
    // print("manual with Ehat");
    // print(inf_emb_man);
    // map the two - they contain almost the same elements, just in different order
    mapping := [];
    for xind in [1..#embedding] do
        x := embedding[xind];
        for yind in [1..#inf_emb_man] do
            if yind in mapping then
                continue yind;
            end if;
            y := inf_emb_man[yind];
            if AbsoluteValue(x - y) le 10^(-6) then
                Append(~mapping, yind);
                continue xind;
            end if;
        end for;
        Append(~mapping, 0);
    end for;
    print("mapping without Ehat -> with Ehat");
    print(mapping);

    return embedding;
end function;

/// Calculate the S-Minkowski Embedding of character(xi) at a finite place of Q
///
/// INPUTS
///  FldNumElt xi in E
///  ModGrpElt in X_E: character of E (formal sum of cosets Gal(Ehat|Q) / Gal(Ehat|E))
///  GrpPerm G Galois-Group of E (Gal(Ehat | Q))
///  RngIntElt prime: place to use
///  Tuple<List[GrpElt in G], List[FldPadElt]>: valuations and local roots over prime
/// OUTPUTS
///  List[sum_{sigma in character-definition} a_sigma -v_P(sigma(xi)) : P in Ehat lies over prime]
/// ASSUMPTIONS
///  Parent(character) eq GModule(G) {so that character can be reduced to a formal sum of roots, which are themselves the GSet of G}
/// ASSUMPTIONS
///  prime must have good reduction in E, i.e.
///  IsSquarefree(PolynomialRing(GF(prime)) ! DefiningPolynomial(AbsoluteField(Parent(xi)))) MUST hold.
function s_minkowski_embedding_at_finite_place(
            xi, character, G, prime, valuation_data
            : precision:=PRECISION_LOW)
    assert IsSquarefree(PolynomialRing(GF(prime)) ! DefiningPolynomial(AbsoluteField(Parent(xi))));
    finite_valuations, padic_roots := Explode(valuation_data);

    // precalculate the possible logarithmic valuation that can be taken
    possible_log_vals := [];
    for i in [1..#padic_roots] do
        at_ith_root := &+[padic_roots[i]^(j - 1) * Eltseq(xi)[j]
                          : j in [1..Degree(Parent(xi))]];
        Append(~possible_log_vals, -Valuation(at_ith_root));
    end for;

    // the empty list to fill with the correct embedding data
    embedding := [RationalField() ! 0 : r in [1..#finite_valuations]];
    eltseq_char := Eltseq(character);
    // these are the cosets of Gal(Ehat | base_field) defining the charactermodule
    cosets := GSet(Group(Parent(character)));

    for i in [1..Dimension(Parent(character))] do
        // skip trivial entries
        if eltseq_char[i] eq 0 then
            continue i;
        end if;

        // sigma is an element of G which is a representative of the coset
        // corresponding to the i-th basis element of Parent(character)
        sigma := cosets[i];

        log_vals := [];
        for tau in finite_valuations do
            // calculate the embedding of tau o sigma (xi) in Q_p^bar
            Append(~log_vals, possible_log_vals[1^(sigma * tau)]);
        end for;

        for place_index in [1..#log_vals] do
            embedding[place_index] +:= eltseq_char[i] * log_vals[place_index];
        end for;
    end for;
    return embedding;
end function;

/// Calculate the S-Minkowski Embedding of char(xi)
///
/// INPUTS
///  FldNumElt xi in E
///  ModGrpElt char in X_E: the character to calculate embedding with
///  RngIntElt set_of_places: Primes to use
///  GrpPerm G Galois-Group of E {Gal(Ehat | Q); first output of GaloisGroup(E) }
///  AssociativeArray{RngIntElt -> Tuple<List[GrpElt in G], List[FldElt]>}:
///      Array that contains for each place in Q the valuations on Ehat above it together with
///      the roots of DefiningPolynomial(E) in a localization over that place
///          (use calculate_finite_valuations or calculate_infinite_valuations for the computation)
/// OUTPUTS
///  List[ReFldElt value of the embedding per dimension] the first #G are the infinite places
///      the last element is the finite place
///
/// NOTES
///  This is not actually the S-Minkowski-Embedding of Ehat.
///  For this we would need to rescale each axis by [Ehat_v : Q_v] / [Ehat : Q]
///  Since we do not know Ehat, we cannot calculate this scaling.
///  But because we only care about kernels and (co-)volumes are irrelevant for us,
///  this does not matter
function s_minkowski_embedding(
        xi, char, set_of_places, G, valuation_data
        : precision:=PRECISION_LOW,
        Ehat:=false, col_dat:=false)

    // infinite places
    embedding_inf := s_minkowski_embedding_at_infinite_places(
        xi, char, G, valuation_data[0]
        : precision:=precision + FORCED_PRECISION_LOSS,
        Ehat:=Ehat, col_dat:=col_dat);
    // finite places


    for place in set_of_places do
        if IsInfinite(place) then
            continue place;
        end if;
        prime := Characteristic(ResidueClassField(place));
        embedding_fin := s_minkowski_embedding_at_finite_place(
            xi, char, G, prime, valuation_data[prime]
            : precision:=precision + FORCED_PRECISION_LOSS);
    end for;

    // throw away some precision
    embedding_inf := [Truncate(x * 10^precision) / 10^precision : x in embedding_inf];
    embedding_fin := [Truncate(x * 10^precision) / 10^precision : x in embedding_fin];
    embedding := embedding_inf cat embedding_fin;
    for x in embedding do
        assert Truncate(x * 10^precision) eq x * 10^precision;
    end for;
    return embedding, embedding_inf, embedding_fin;
end function;


function _embedding_at_single_character_fixed_precision(
        base_char_index, E, X_E, OES_times_to_E, O_E_S_times,
        G, set_of_places, valuation_data, precision : Ehat:=false, col_dat:=false)
    // Inner function for lattice_at_single_character
    //
    // NOTES
    //  this function DOES NOT return proven results
    embs := [];
    embs_inf := [];
    embs_fin := [];
    gen_index := 0;
    for i in [1..#Generators(O_E_S_times)] do
        if not Order(O_E_S_times.i) eq 0 then
            continue i;
        end if;
        gen_index +:= 1;
        embedding, embedding_inf, embedding_fin := s_minkowski_embedding(
            E!OES_times_to_E(O_E_S_times.i),
            X_E.base_char_index,
            set_of_places,
            G,
            valuation_data
            : precision := precision,
            Ehat:=Ehat, col_dat:=col_dat);
        Append(~embs, Vector(#embedding, embedding));
        Append(~embs_inf, Vector(#embedding_inf, embedding_inf));
        Append(~embs_fin, Vector(#embedding_fin, embedding_fin));
    end for;
    return embs, embs_inf, embs_fin;
end function;

function lattice_at_single_character(
        base_char_index, E, X_E, OES_times_to_E, O_E_S_times,
        G, set_of_places, valuation_data: Ehat:=false, col_dat:=false)
    // Calculate the Image lattice of a single character
    //
    // NOTES
    //  This function return proven results
    //  in particular, it abstracts away handling of machine error

    try_precision := PRECISION_LOW;
    while true do
        // TODO rename this; emb is a terrible name
        emb, emb_inf, emb_fin := _embedding_at_single_character_fixed_precision(
            base_char_index, E, X_E, OES_times_to_E, O_E_S_times,
            G, set_of_places, valuation_data, try_precision + FORCED_PRECISION_LOSS
            : Ehat:=Ehat, col_dat:=col_dat);

        // now try to prove the result
        m := Matrix(emb);
        basis, trafo, rank := LLL(m);
        // throw away precision from basis - it is calculated
        // using float multiplication, but we need it later to create a lattice
        tmp := 10^try_precision * basis;
        floored_basis := Matrix([
            [
                Truncate(tmp[i][j]) / 10^try_precision
                : j in [1..NumberOfColumns(tmp)]
            ]
            : i in [1..NumberOfRows(tmp)]
        ]);

        gram_schmidt := Orthogonalize(basis);
        // note the cutoff after rank - all other rows
        // correspond to elements of basis which are 0-rows
        // - we do not care about these rows or their transforms
        svp_lower_bound := Minimum(
            [&+[AbsoluteValue(gram_schmidt[i,j])
                : j in [1..NumberOfColumns(gram_schmidt)]]
             : i in [1..rank]]);
        max_allowable_machine_error := svp_lower_bound / (2 * Maximum(
            [&+[AbsoluteValue(trafo[i,j])
                : j in [1..NumberOfColumns(trafo)]]
             : i in [1..rank]]));

        if 10^(-try_precision) lt max_allowable_machine_error then
            floored_lat := Lattice(floored_basis);
            lat := Lattice(basis);
            // for every element of emb:
            // get its integral decomp in lat and
            // return the same element in floored_lat
            floored_embs := [floored_lat |];
            for image_of_gen in emb do
                coordinates_in_lattice := Coordinates(lat ! image_of_gen);
                Append(~floored_embs, &+[Basis(floored_lat)[i] * coordinates_in_lattice[i]
                                         : i in [1..Dimension(floored_lat)]]);
            end for;
            return floored_lat, floored_embs, emb_inf, emb_fin;
        end if;

        // retry with higher precision
        try_precision *:= 2;
    end while;
end function;

/// Calculate the Lattice in S-Minkowski Space generated by images of characters
///
/// INPUTS
///  FldNum E to embed
///  List[PlcNumElt] set_of_places : places of E to embed at (this is S)
///  GrpPerm G: GaloisGroup(Ehat | Q)
///  ModGrp X_E: the Charactermodule of E^x
/// OUTPUTS
///  List[List[FldReElt Images of all generators under one character] | character]
///  Lat: the complete S-minkowski lattice
///  GrpAb: S-Unit Group of E
///  Map[GrpAb, FldNum]: map from the s-units to E
function image_lattice(E, set_of_places, G, X_E
        : debug_chars:=false, debug_col_dat:=false)
    places_in_E := [];
    for place in set_of_places do
        if IsInfinite(place) then
            continue place;
        end if;
        p := Characteristic(ResidueClassField(place));
        places_in_E cat:= [Ideal(el[1]) : el in Decomposition(E, p)
                           | Extends(el[1], place)];
    end for;
    // we need to absolutize these ideals for SUnitGroup to work
    E_abs := AbsoluteField(E);
    O := MaximalOrder(E_abs);
    O_E_S_times, S_units_to_E := SUnitGroup(
        [ideal<O | [E_abs ! x : x in Generators(el)]>
         : el in places_in_E]);
    Ehat := NormalClosure(E_abs);

    // we calculate the valuations here to prevent recalculation later.
    // see the comments in s_minkowski_embedding_at_finite_place and ...infinite... for more details
    valuation_data := AssociativeArray();
    // infinite valuation is always necessary
    valuations, roots := calculate_infinite_valuations(G, E);

    valuation_data[0] := [*valuations, roots*];
    for place in set_of_places do
        if IsInfinite(place) then
            continue place;
        end if;
        prime := Characteristic(ResidueClassField(place));
        valuations, roots := calculate_finite_valuations(G, E, prime);

        valuation_data[prime] := [*valuations, roots*];
    end for;

    // List[List[Images of all generators under one character] | character]
    embs := [**];
    embs_inf := [**];
    embs_fin := [**];
    lattices := [];
    for base_char_index in [1..Dimension(X_E)] do
        lattice, embs_at_bci, embs_at_bci_inf, embs_at_bci_fin := lattice_at_single_character(
            base_char_index, E, X_E, S_units_to_E, O_E_S_times,
            G, set_of_places, valuation_data
            : Ehat:=Ehat, col_dat:=debug_col_dat);
        Append(~embs, embs_at_bci);
        Append(~embs_inf, embs_at_bci_inf);
        Append(~embs_fin, embs_at_bci_fin);
        Append(~lattices, lattice);
    end for;

    matrices := [];
    matrices_inf := [];
    matrices_fin := [];
    for character in debug_chars do
        rows := [];
        rows_inf := [];
        rows_fin := [];
        // each generator gets one row
        for gen_index in [1..#embs[1]] do
            // we need to add the contributions from all the base-characters
            Append(~rows, Eltseq(
                &+[Eltseq(character)[base_char_index] * embs[base_char_index][gen_index]
                : base_char_index in [1..Dimension(Parent(character))]]
            ));
            Append(~rows_inf, Eltseq(
                &+[Eltseq(character)[base_char_index] * embs_inf[base_char_index][gen_index]
                : base_char_index in [1..Dimension(Parent(character))]]
            ));
            Append(~rows_fin, Eltseq(
                &+[Eltseq(character)[base_char_index] * embs_fin[base_char_index][gen_index]
                : base_char_index in [1..Dimension(Parent(character))]]
            ));
        end for;
        Append(~matrices, Matrix(Rationals(), rows));
        Append(~matrices_inf, Matrix(Rationals(), rows_inf));
        Append(~matrices_fin, Matrix(Rationals(), rows_fin));
    end for;

    print("the kernels from the S-minkowski embedding");
    for i in [1..#debug_chars] do
    ker := [[RealField(30) ! x : x in Eltseq(el)] : el in Basis(Kernel(matrices[i]))];
    ker_inf := [[RealField(30) ! x : x in Eltseq(el)] : el in Basis(Kernel(matrices_inf[i]))];
    ker_fin := [[RealField(30) ! x : x in Eltseq(el)] : el in Basis(Kernel(matrices_fin[i]))];
    print(<debug_chars[i],
             ker,
             ker_inf,
             ker_fin
            >
    );
    end for;


    // get O_Ehat_S
    Ohat := MaximalOrder(Ehat);
    places_in_Ehat := [
        Ideal(q[1])
        : q in Decomposition(Ehat, Characteristic(ResidueClassField(place))), place in set_of_places];
    O_Ehat_S_times, O_Ehat_S_to_Ehat := SUnitGroup(places_in_Ehat);


    // print("DEBUG: the characters to kill");
    // print(debug_chars);
    // print("the subspaces spanned by each of these");
    // print([sub<Universe(debug_chars) | el> : el in debug_chars]);
    // print("the subspace spanned by all of them together");
    // print(sub<Universe(debug_chars) | debug_chars>);
    kill_as_s_unit := [X_E ! el : el in Basis(sub<Universe(debug_chars) | debug_chars>)];
    killers_on_xs := [debug_col_dat`characterQuotientHom(el) : el in kill_as_s_unit];
    // print("the characters to kill pushed into X_S");
    // print(killers_on_xs);

    // print("the basis of Image(characterQuotientHom) pulled into X_E");
    X_S := Codomain(debug_col_dat`characterQuotientHom);
    // print([X_E ! el : el in Basis(Kernel(debug_col_dat`characterQuotientHom))]);

    // write out characters as hom<O_E_S_times -> O_Ehat_S>
    chars_as_S_unit_maps := [];
    for char in debug_chars do
        Append(~chars_as_S_unit_maps,
            hom<O_E_S_times -> O_Ehat_S_times |
                SUnitDiscLog(
                    O_Ehat_S_to_Ehat,
                    [
                        _ApplyCharacter(
                            char,
                            E ! S_units_to_E(O_E_S_times.i),
                            debug_col_dat
                            : Ehat:=Ehat)
                        : i in [1..Ngens(O_E_S_times)]
                    ],
                    places_in_Ehat
                )
            >);
    end for;
    com_ker := &meet[Kernel(x) : x in chars_as_S_unit_maps];
    // print("the common kernel on the s units");
    // print(com_ker);
    y := com_ker.2;
    z := E ! S_units_to_E(y);


    // NOTEs für morgen:
    // probier mal, die S-minkowski-Einbettung per Hand mit Ehat auszurechnen
    // (also stellen zerlegen, bewertungen ausrechnen)
    // und vergleiche das
    //  - mit valuation_data
    //  - mit der Einbettung
    // fällt irgendwas auf, was an der berechnung ohne Ehat falsch sein könnte?
    // print("infinite places in Ehat");
    // print(InfinitePlaces(Ehat));
    // print("finite places in Ehat");
    // print(places_in_Ehat);
    // print("nacheinander die valuation-data ohne Ehat ausgerechnet");
    // print("unendliche stelle");
    // print(valuation_data[0]);
    // for p in set_of_places do
    //     prime := Characteristic(ResidueClassField(p));
    //     printf "at %o\n", prime;
    //     print(valuation_data[prime]);
    // end for;

    return embs, &+lattices, O_E_S_times, S_units_to_E;
end function;

/// Calculate a single characters map as a Z-Matrix
///
/// INPUTS
///  GrpModElt character: The character to calculate as a Z-Matrix
///  List[List[Vector]] embs: the embeddings as given by image_lattice
///  Lat lattice: the lattice given by image_lattice
/// OUTPUTS
///  Matrix containing the images of the generators of O_E,S in Basis(lattice) under character as rows
function single_character_as_z_matrix(character, embs, lattice)
    rows := [];
    row_space := RSpace(Integers(), Dimension(lattice));
    // each generator gets one row
    for gen_index in [1..#embs[1]] do
        Append(~rows, row_space ! 0);
        // we need to add the contributions from all the base-characters
        for base_char_index in [1..Dimension(Parent(character))] do
            image_in_lattice := Eltseq(character)[base_char_index] * embs[base_char_index][gen_index];
            coordinates_in_lattice := row_space ! Coordinates(lattice ! image_in_lattice);
            rows[gen_index] +:= coordinates_in_lattice;
        end for;
    end for;
    return Matrix(rows);
end function;

/// calculate the common matrix that defines the action of all characters on the generators of O_E,S
///
/// INPUTS
///  GrpModElt character: The character to calculate as a Z-Matrix
///  List[List[Vector]] embs: the embeddings as given by image_lattice
///  Lat lattice: the lattice given by image_lattice
/// OUTPUTS
///  Matrix containing the images of the generators of O_E,S in Basis(lattice)
///      for each character, such a block is constructed and horizontally joined such that
///      Kernel(res) = \cap Kernel(single_character_matrix)
function calculate_characters_as_z_matrix(characters, embs, lattice)
    return HorizontalJoin(
        [single_character_as_z_matrix(char, embs, lattice)
         : char in characters]);
end function;

/// Find an element of the S-Units of E on which all characters vanish
///
/// INPUTS
///  FldNum E: Field to search in
///  SeqEnum[GrpModElt] characters: characters to kill
///  List[RngIntElt or Infinity()] set_of_places: the places to use
///  GrpPerm G: galois-Group Gal(Ehat|Q)
/// OUTPUTS
///  FldNumElt e in E^x on which all characters vanish and which is an S-Unit
/// ASSUMPTIONS
///  The characters need to have a common zero in the S-Units
function find_common_zero_of_characters(E, characters, set_of_places, collateral_data)
    G := collateral_data`galoisGroupOverQ;

    places_in_E := [];
    for place in set_of_places do
        if IsInfinite(place) then
            continue place;
        end if;
        p := Characteristic(ResidueClassField(place));
        places_in_E cat:= [Ideal(el[1]) : el in Decomposition(E, p)
                           | Extends(el[1], place)];
    end for;
    E_abs := AbsoluteField(E);
    O := MaximalOrder(E_abs);
    O_E_S_times, S_units_to_E := SUnitGroup(
        [ideal<O | [E_abs ! x : x in Generators(el)]>
         : el in places_in_E]);
    Ehat := NormalClosure(E_abs);
    Ohat := MaximalOrder(Ehat);
    places_in_Ehat := [
        Ideal(q[1])
        : q in Decomposition(Ehat, Characteristic(ResidueClassField(place))), place in set_of_places];
    O_Ehat_S_times, O_Ehat_S_to_Ehat := SUnitGroup(places_in_Ehat);

    // write out characters as hom<O_E_S_times -> O_Ehat_S>
    chars_as_S_unit_maps := [];
    for char in characters do
        chars_applied := [
            _ApplyCharacter(
                char,
                E ! S_units_to_E(O_E_S_times.i),
                collateral_data
                : Ehat:=Ehat)
            : i in [1..Ngens(O_E_S_times)]
        ];
        Append(~chars_as_S_unit_maps,
            hom<O_E_S_times -> O_Ehat_S_times |
                SUnitDiscLog(
                    O_Ehat_S_to_Ehat,
                    [
                        _ApplyCharacter(
                            char,
                            E ! S_units_to_E(O_E_S_times.i),
                            collateral_data
                            : Ehat:=Ehat)
                        : i in [1..Ngens(O_E_S_times)]
                    ],
                    places_in_Ehat
                )
            >);
    end for;

    com_ker := &meet[Kernel(x) : x in chars_as_S_unit_maps];

    // print("TODO DEBUG");
    // print(set_of_places);
    // print("decomposition into Ehat");
    // print([x[2] : x in Decomposition(Ehat, Characteristic(ResidueClassField(p))), p in set_of_places]);
    // print("good reduction?");
    // print([
    //     Factorization(
    //         PolynomialRing(GF(Characteristic(ResidueClassField(p)))) !
    //         DefiningPolynomial(AbsoluteField(Ehat)))
    //     : p in set_of_places
    // ]);


    for x in Generators(com_ker) do
        if Order(x) eq 0 then
            print("\n\n\n***********found generator");
            print(E ! S_units_to_E(x));
            print("at places");
            print(set_of_places);
            return E ! S_units_to_E(x);
        end if;
    end for;

    "\n\n\n***********";
    "\nBEGIN DEBUG OUTPUT";
    E; characters; set_of_places; collateral_data;
    com_ker; [Kernel(x) : x in chars_as_S_unit_maps];
    // TODO
    return false;
    // END TODO
    assert "No generator was found, even though all requirements were asserted" cmpeq false;
end function;
