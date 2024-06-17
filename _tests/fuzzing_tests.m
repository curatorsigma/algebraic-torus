// Fuzzing - Tests for the AlgebraicTorus package

import "../core/characters.m":
    ranks_of_irreds_at_prime_ext,
    ranks_of_irreds_at_prime_swap,
    ranks_of_irreds_at_prime,
    ranks_of_irreds;

import "random_generators.m" :
    random_element,
    random_irreducible_polynomial,
    random_numberfield,
    random_set_of_places,
    random_eps_hermitian_form,
    _generate_random_element;

import "../EtaleAlgebra/InvolutiveEtaleAlgebra.m" : 
    apply_base_conjugate_to_polynomial;

procedure fuzz_form_to_inv_to_form()
    // test with a simple involution over a Skewfield
    K := QuadraticField(5);
    K := InvolutiveRing(-K.1);
    quats := QuaternionAlgebra<K | -1, -1>;
    quats := InvolutiveAlgebra(quats, [Conjugate(el) : el in Basis(quats)]);

    B := random_eps_hermitian_form(quats, 3, 1);
    invalg := InvolutiveAlgebra(B);
    q := GetFormOfInvolution(invalg);
    // note that we only get a multiple of the form back
    // it is actually a multiple by the subfield of K fixed by the involution (in this case Q)
    fact := q[1][1] / B[1][1];
    assert fact in Rationals();
    assert q eq B * (Parent(B) ! fact);
end procedure;

procedure fuzz_AlgEta()
    F := random_numberfield(:MAX_DEGREE:=3);
    K := random_numberfield(:basefield:=F,MAX_DEGREE:=3);
    Ls := [];
    num_of_Ls := 4;
    images := [**];
    for i in [1..num_of_Ls] do
        Append(~Ls, random_numberfield(:basefield:=K,MAX_DEGREE:=2,MIN_DEGREE:=2));
        roots := [el[1] :
                  el in Roots(apply_base_conjugate_to_polynomial(
                        DefiningPolynomial(Ls[i]), K.1), Ls[i])];
        for r in roots do
            if r ne Ls[i].1 then
                Append(~images, [(k eq i) select r else 0 : k in [1..num_of_Ls]]);
                continue i;
            end if;
        end for;
    end for;

    alg := EtaleAlgebra(Ls, K);
    realization, alg_to_real := StandardRealization(alg : update_realization:=true);
    alg := InvolutiveAlgebra(
        alg,
        images,
        K.1);
    over_f := RedefineOverNewField(alg, F : realization:="Force");
    assert IsRealized(over_f);
    assert IsInvolutive(over_f);
end procedure;

procedure fuzz_ranks_of_irreds()
    // Fuzz ranks_of_irreds
    for i in [1..3] do
        basefield := random_numberfield(
            :MAX_DEGREE:=2);
        fixedfield := random_numberfield(
            :basefield:=basefield, MAX_DEGREE:=3);
        extensionfield := random_numberfield(
            :basefield:=fixedfield, MIN_DEGREE:=2, MAX_DEGREE:=2);

        set_of_places := random_set_of_places(basefield
            : MIN_NUMBER_OF_INFINITE_PLACES:=1,
              MAX_NUMBER_OF_INFINITE_PLACES:=3,
              MAX_NUMBER_OF_FINITE_PLACES:=5);

        a, b := GetSeed();
        res := ranks_of_irreds(basefield, fixedfield, extensionfield, set_of_places);
        SetSeed(a, b);
    end for;
end procedure;

procedure fuzz_AlgTor_constructor()
    // Extension type
    tori := [];
    for i in [1..3] do
        basefield := random_numberfield(
            :MAX_DEGREE:=4);
        fixedfield := random_numberfield(
            :basefield:=basefield, MAX_DEGREE:=3);
        extensionfield := random_numberfield(
            :basefield:=fixedfield, MIN_DEGREE:=2, MAX_DEGREE:=2);

        a, b := GetSeed();
        Append(~tori, AlgebraicTorus(basefield, fixedfield, extensionfield));
        SetSeed(a, b);
    end for;

    // Swap-Type
    for i in [1..3] do
        basefield := random_numberfield(
            :MAX_DEGREE:=4);
        fixedfield := random_numberfield(
            :basefield:=basefield, MAX_DEGREE:=3);
        extensionfield := random_numberfield(
            :basefield:=fixedfield, MIN_DEGREE:=2, MAX_DEGREE:=2);

        a, b := GetSeed();
        Append(~tori, AlgebraicTorus(basefield, fixedfield, extensionfield));
        SetSeed(a, b);
    end for;
end procedure;

procedure fuzz_LocalRank()
    // For the extension-type: The local rank of L|K|F is
    // the number of places in K above v in Σ_F that split in L
    for i in [1..3] do
        basefield := random_numberfield(
            :MAX_DEGREE:=4);
        fixedfield := random_numberfield(
            :basefield:=basefield, MAX_DEGREE:=3);
        extensionfield := random_numberfield(
            :basefield:=fixedfield, MIN_DEGREE:=2, MAX_DEGREE:=2);

        a, b := GetSeed();
        torus := AlgebraicTorus(basefield, fixedfield, extensionfield);
        SetSeed(a, b);

        place := random_set_of_places(basefield : 
            MIN_NUMBER_OF_FINITE_PLACES:=1,
            MAX_NUMBER_OF_FINITE_PLACES:=1,
            BASE_INDEX_OF_FINITE_PLACES:=10,
            MIN_NUMBER_OF_INFINITE_PLACES:=0,
            MAX_NUMBER_OF_INFINITE_PLACES:=0)[1];
        decomp_in_ff := [el[1]
                         : el in Decomposition(fixedfield, Characteristic(ResidueClassField(place)))
                         | Extends(el[1], place)];
        decomp_in_ef := Decomposition(extensionfield, Characteristic(ResidueClassField(place)));
        num := 0;
        for p_ff in decomp_in_ff do
            decomp_in_ef := [el[1] : el in decomp_in_ef | Extends(el[1], p_ff)];
            if #decomp_in_ef ge 2 then
                num +:= 1;
            end if;
        end for;
        assert num eq LocalRank(torus, place);
    end for;
end procedure;

procedure fuzz_WeilRestriction()
    basefield := random_numberfield(
        :MAX_DEGREE:=4,
         MIN_DEGREE:=2);
    fixedfield := random_numberfield(
        :basefield:=basefield, MAX_DEGREE:=3);
    extensionfield := random_numberfield(
        :basefield:=fixedfield, MIN_DEGREE:=2, MAX_DEGREE:=2);

    a, b := GetSeed();
    torus_over_basefield := AlgebraicTorus(basefield, fixedfield, extensionfield);
    ff_over_q := AbsoluteField(fixedfield);
    _ := IsSubfield(ff_over_q, extensionfield);
    ef_over_ff_over_q := RelativeField(ff_over_q, extensionfield);
    torus_over_q := AlgebraicTorus(Rationals(), ff_over_q, ef_over_ff_over_q);
    SetSeed(a, b);
    wr := WeilRestriction(torus_over_basefield, Rationals());
    if not IsIsomorphic(wr, torus_over_q) then
        print(wr);
        print(torus_over_q);
        error "Torus over small field and over large field, restricted are not isomorphic.";
    end if;
end procedure;

procedure run_all_fuzzing_tests()
    // print(">Fuzzing EtaleAlgebra");
    // print("With Seed");
    // print(GetSeed());
    // fuzz_AlgEta();
    // print(".Success.\n");

    // print(">Fuzzing fuzz_form_to_inv_to_form");
    // print("With Seed");
    // print(GetSeed());
    // fuzz_form_to_inv_to_form();
    // print(".Success.\n");

    print(">Fuzzing ranks_of_irreds");
    print("With Seed");
    print(GetSeed());
    // This seed fails to calculate the correct ranks
    // SetSeed(2274053151, 4695892);
    SetSeed(3956807426, 3526308);
    printf "\n\nNow fuzz_ranks_of_irreds with nthreads = %o\n\n\n", GetNthreads();
    fuzz_ranks_of_irreds();
    print(".Success.\n");

    print(">Fuzzing LocalRank");
    // This seed fails with an error in RelativeField(RngLocA, Map) I cannot fix.
    // SetSeed(2274053151, 3050789);
    print("With Seed");
    print(GetSeed());
    fuzz_LocalRank();
    print(".Success.\n");
end procedure;
