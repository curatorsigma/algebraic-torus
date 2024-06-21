// unit tests for the AlgebraicTorus package

import "../EtaleAlgebra/EtaleAlgebra.m":
    _choose_elements;

import "../core/characters.m":
    ranks_of_irreds_at_prime_ext,
    ranks_of_irreds_at_prime_swap,
    ranks_of_irreds_at_prime,
    ranks_of_irreds_at_infinity_ext,
    ranks_of_irreds_at_infinity_swap,
    ranks_of_irreds_at_infinity,
    ranks_of_irreds;

import "../core/primitives.m":
    cast_from_FldPad_to_RngLocA,
    coordinates_in_basis,
    find_isomorphism_type,
    decomposition_but_works,
    cut_precision_to_n,
    mtrx_cut_precision_to_n,
    fldreelt_to_fldratelt;

import "random_generators.m" :
    random_eps_hermitian_form;

procedure test_precision_cuts()
    RR := RealField(20);
    x := RR ! 1234.13413675341;
    assert cut_precision_to_n(x, 5) eq 1234.13413;
    assert cut_precision_to_n(RR ! 0.804718956217, 9) eq 0.804718956;


    m := Matrix(RR, 2, 2, [[1.513, 9.15278], [3, 911.3]]);
    res := mtrx_cut_precision_to_n(m, 2);
    assert res eq Matrix(RR, 2, 2, [[1.51, 9.15], [3, 911.3]]);

    assert fldreelt_to_fldratelt(0.52000000p8) eq 13 / 25;
end procedure;

procedure test_choose_elements()
    lists := [[1, 2, 3], [3], [1, 2], [4]];
    success, result := _choose_elements(lists);
    assert success;
    assert result eq [1, 3, 2, 4];

    lists := [[1], [1], [2, 3], [2, 3]];
    success, result := _choose_elements(lists);
    assert not success;
end procedure;

procedure run_RngPad_cast()
    R<x> := PolynomialRing(Integers());
    L<a> := UnramifiedExtension(pAdicRing(5, 10), x^5 + x^2 + 2);
    local_ring := TotallyRamifiedExtension(L, x^4 + 5);
    res, map := cast_from_FldPad_to_RngLocA(local_ring);
    if not Type(res) eq RngLocA then
        print(Type(res));
        error "cast returned wrong type";
    end if;

    if not AbsoluteDegree(res) eq AbsoluteDegree(local_ring) then
        error "RngLocA has wrong dimension";
    end if;

    x := local_ring.1^2 + 2 * local_ring.1 - local_ring ! 1;
    image := map(x);
    assert x eq Inverse(map)(image);
end procedure;

procedure run_ranks_of_irreds_at_prime_ext()
    K := NumberField(Polynomial([1, 0, 1]));
    R<x> := PolynomialRing(K);
    F := NumberField(x^3 - 2);
    E := ext<F | x^2 - 5>;
    place := Decomposition(K, 13)[1][1];

    irreds, qranks, pranks, collateral_data := ranks_of_irreds_at_prime_ext(K, F, E, place);
    if not Dimension(Codomain(collateral_data`characterQuotientHom)) gt 0 then
        error "Got a trivial module in extension case at finite place.";
    end if;


    K := NumberField(Polynomial([8, -5, 1]));
    R<x> := PolynomialRing(K);
    F := ext<K |x^3 + (3*K.1 + 7)*x^2 + (-8*K.1 - 4)*x + 8*K.1 - 7>;
    S<y> := PolynomialRing(F);
    E := ext<F | y^2 + (8*F.1^2 - F.1 - 2)*y - 6*F.1^2 - 6*F.1 + 1>;
    place := Decomposition(K, 2)[1][1];
    SetSeed(1448797384, 21686);
    irreds, qranks, pranks, collateral_data := ranks_of_irreds_at_prime_ext(K, F, E, place);
    if not Dimension(Codomain(collateral_data`characterQuotientHom)) gt 0 then
        error "Got a trivial module in extension case at finite place.";
    end if;
end procedure;

procedure run_ranks_of_irreds_at_prime_swap()
    K := NumberField(Polynomial([1, 0, 1]));
    R<x> := PolynomialRing(K);
    F := NumberField(x^3 - 2);
    place := Decomposition(K, 13)[1][1];

    irreds, qranks, pranks, collateral_data := ranks_of_irreds_at_prime_swap(K, F, place);
    if not Dimension(Codomain(collateral_data`characterQuotientHom)) gt 0 then
        error "Got a trivial module in extension case at finite place.";
    end if;

    // a place with bad reduction
    BF := QNF();
    place := Decomposition(BF, 13)[1][1];
    FF := ext<BF | Polynomial(
        BF, [277169, 21720, -88656, -75380, 42636, 11040, -6186, 0,
             624, -20, -36, 0, 1])>;
    irreds, qranks, pranks, collateral_data := ranks_of_irreds_at_prime_swap(
        BF, FF, place);
end procedure;

procedure run_ranks_of_irreds_at_prime()
    K := NumberField(Polynomial([1, 0, 1]));
    R<x> := PolynomialRing(K);
    F := NumberField(x^3 - 2);
    E := ext<F | x^2 - 5>;
    place := Decomposition(K, 13)[1][1];

    irreds, qranks, pranks, collateral_data := ranks_of_irreds_at_prime(K, F, E, place);
    if not Dimension(Codomain(collateral_data`characterQuotientHom)) gt 0 then
        error "Got a trivial module in extension case at finite place.";
    end if;

    irreds, qranks, pranks, collateral_data := ranks_of_irreds_at_prime(K, F, F, place);
    if not Dimension(Codomain(collateral_data`characterQuotientHom)) gt 0 then
        error "Got a trivial module in extension case at finite place.";
    end if;
end procedure;

procedure run_ranks_of_irreds_at_infinity_ext()
    K := NumberField(Polynomial([1, 0, 1]));
    R<x> := PolynomialRing(K);
    F := NumberField(x^3 - 2);
    E := ext<F | x^2 - 5>;
    place := InfinitePlaces(K)[1];

    irreds, qranks, pranks, collateral_data := ranks_of_irreds_at_infinity_ext(K, F, E, place);
    if not Dimension(Codomain(collateral_data`characterQuotientHom)) gt 0 then
        error "Got a trivial module in extension case at finite place.";
    end if;
end procedure;

procedure run_ranks_of_irreds_at_infinity_swap()
    K := NumberField(Polynomial([1, 0, 1]));
    R<x> := PolynomialRing(K);
    F := NumberField(x^3 - 2);
    place := InfinitePlaces(K)[1];

    irreds, qranks, pranks, collateral_data := ranks_of_irreds_at_infinity_swap(K, F, place);
    if not Dimension(Codomain(collateral_data`characterQuotientHom)) gt 0 then
        error "Got a trivial module in swap case at infinite place.";
    end if;
end procedure;

procedure run_ranks_of_irreds_at_infinity()
    K := NumberField(Polynomial([1, 0, 1]));
    R<x> := PolynomialRing(K);
    F := NumberField(x^3 - 2);
    E := ext<F | x^2 - 5>;
    place := InfinitePlaces(K)[1];

    irreds, qranks, pranks, collateral_data := ranks_of_irreds_at_infinity(K, F, E, place);
    if not Dimension(Codomain(collateral_data`characterQuotientHom)) gt 0 then
        error "Got a trivial module in extension case at infinite place.";
    end if;

    irreds, qranks, pranks, collateral_data := ranks_of_irreds_at_infinity(K, F, F, place);
    if not Dimension(Codomain(collateral_data`characterQuotientHom)) gt 0 then
        error "Got a trivial module in swap case at infinite place.";
    end if;
end procedure;

procedure run_ranks_of_irreds()
    K := NumberField(Polynomial([1, 0, 1]));
    R<x> := PolynomialRing(K);
    F := NumberField(x^3 - 2);
    E := ext<F | x^2 - 5>;
    place := Decomposition(K, 13)[1][1];
    place2 := InfinitePlaces(K)[1];

    irreds, ranks, collateral_data := ranks_of_irreds(K, F, F, [*place, place2*]);
    if not #irreds eq #ranks then
        error "Size of output-Arrays is wrong.";
    end if;
    if not Dimension(Codomain(collateral_data`characterQuotientHom)) gt 0 then
        error "Got a trivial module.";
    end if;

    // Test that passing Infinity() and finite primes as places also works
    K := QuadraticField(-1);
    R<x> := PolynomialRing(K);
    E := ext<K | x^2 - 5>;
    irreds, ranks, collateral_data := ranks_of_irreds(Rationals(), K, E, [*Infinity(), 7*]);

    // run defined test on Q(i)
    irreds, ranks, collateral_data := ranks_of_irreds(Rationals(), K, K, [*Infinity(), 7, 11*]);
    if not ranks[1][0] + ranks[2][0] eq 1 then
        error "Wrong result in Swap-Case global rank.";
    end if;
    if not ranks[1][1] + ranks[2][1] eq 1 then
        error "Wrong result in Swap-Case local rank at infinity.";
    end if;
    if not ranks[1][2] + ranks[2][2] eq 1 then
        error "Wrong result in Swap-Case local rank at finite.";
    end if;
end procedure;

procedure construct_AlgebraicTorusIrred()
    // Test the various Constructors for AlgebraicTorusIrred

    K := NumberField(Polynomial([1, 0, 1]));
    R<x> := PolynomialRing(K);
    F := NumberField(x^3 - 2);
    E := ext<F | x^2 - 5>;
    place := Decomposition(K, 13)[1][1];

    irreds, ranks, collateral_data := ranks_of_irreds(K, F, E, [place]);

    torus := AlgebraicTorusIrred(
        [K, F, E], irreds[1],
        collateral_data);
end procedure;

procedure construct_AlgebraicTorus()
    K := NumberField(Polynomial([1, 0, 1]));
    R<x> := PolynomialRing(K);
    F := NumberField(x^3 - 2);
    E := ext<F | x^2 - 7>;

    // test the trivial constructor
    torus1 := AlgebraicTorus(K);
    torus2 := AlgebraicTorus(Rationals());
    assert torus1 ne torus2;

    // test the basic constructor
    torus := AlgebraicTorus(K, F, E : Prime:=13);
    assert torus eq torus;

    // test the basic constructor over Rationals()
    torus := AlgebraicTorus(Rationals(), F, E : Prime:=13);

    // test the etale-algebra constructor
    torus := AlgebraicTorus(
        K,
        [<F, F>, <F, E>] : Prime:=23);
    if not Dimension(torus) eq 6 then
        error "AlgebraicTorus returned with the wrong dimension.";
    end if;
    if not torus`baseField eq K then
        error "AlgebraicTorus from etale Algebra set wrong base Field.";
    end if;

    // test the etale-algebra constructor over Rationals()
    torus := AlgebraicTorus(
        Rationals(),
        [<F, F>, <F, E>] : Prime:=23);
    if not Dimension(torus) eq 12 then
        error "AlgebraicTorus returned with the wrong dimension.";
    end if;
    if not AbsoluteDegree(torus`baseField) eq 1 then
        error "AlgebraicTorus from etale Algebra set wrong base Field.";
    end if;
end procedure;

procedure run_IsIsomorphic()
    K := NumberField(Polynomial([1, 0, 1]));
    R<x> := PolynomialRing(K);
    F := NumberField(x^3 - 2);
    E := ext<F | x^2 - 7>;
    E_a := AbsoluteField(E);
    _ := IsSubfield(F, E_a);
    E2 := RelativeField(F, E_a);

    torus := AlgebraicTorus(K, F, E : Prime:=13);
    if not IsIsomorphic(torus, torus) then
        error "A torus is not isomorphic to itself.";
    end if;
    torus2 := AlgebraicTorus(K, F, E2 : Prime:=17);
    if not IsIsomorphic(torus, torus2) then
        error "Two isomorphic tori are not seen as isomorphic.";
    end if;
end procedure;

procedure run_DirectProduct()
    K := NumberField(Polynomial([1, 0, 1]));
    R<x> := PolynomialRing(K);
    F := NumberField(x^3 - 2);
    E := ext<F | x^2 - 5>;

    torus := AlgebraicTorus(K, F, E : Prime:=13);

    F := NumberField(x^3 - 5);
    E := ext<F | x^2 - 7>;

    torus2 := AlgebraicTorus(K, F, E : Prime:=13);

    product_torus := DirectProduct(torus, torus2);
    if not Dimension(product_torus) eq Dimension(torus) + Dimension(torus2) then
        error "Product torus has wrong dimension";
    end if;
    if not product_torus`baseField eq torus`baseField then
        error "Product torus has the wrong baseField";
    end if;

    product_torus2 := DirectProduct([torus, torus2]);
    if not Dimension(product_torus2) eq Dimension(torus) + Dimension(torus2) then
        error "Product torus has wrong dimension";
    end if;
    if not product_torus2`baseField eq torus`baseField then
        error "Product torus has the wrong baseField";
    end if;

    // test a more complicated direct product
    product_torus3 := DirectProduct([torus, torus, torus2, torus]);
end procedure;

procedure run_WeilRestriction()
    SetSeed(2274053151, 222884);
    K := NumberField(Polynomial([1, 0, 1]));
    R<x> := PolynomialRing(K);
    F := NumberField(x^3 - 7);
    E := ext<F | x^2 - 19>;
    place := Decomposition(K, 13)[1][1];

    irreds, ranks, collateral_data := ranks_of_irreds(K, F, E, [place]);

    torus := AlgebraicTorusIrred(
        [K, F, E], irreds[1],
        collateral_data);
    restriction := WeilRestriction(torus, Rationals());
    if not IsIsomorphic(restriction`baseField, QNF()) then
        error "WeilRestriction did not work.";
    end if;
    if not Dimension(restriction) eq 2 * Dimension(torus) then
        error "WeilRestriction returned wrong dimension.";
    end if;

    // test Weil-Restriction on a non irreducible torus.
    torus := AlgebraicTorus(K, F, E : Prime:=13);
    restriction := WeilRestriction(torus, Rationals());

    F_a := AbsoluteField(F);
    E_a := AbsoluteField(E);
    _ := IsSubfield(F_a, E_a);
    E2 := RelativeField(F_a, E_a);
    torus_over_q := AlgebraicTorus(
        Rationals(), F_a, E2 : Prime:=13);
    if not IsIsomorphic(restriction, torus_over_q) then
        error "Torus over small field and over large field, restricted are not isomorphic.";
    end if;
end procedure;

procedure rank_of_torus()
    K := NumberField(Polynomial([1, 0, 1]));
    R<x> := PolynomialRing(K);
    F := NumberField(x^3 - 2);
    E := ext<F | x^2 - 7>;

    torus1 := AlgebraicTorus(K, F, E : Prime:=13);
    res := LocalRank(torus1, Decomposition(K, 13)[1][1]);
    if not Type(res) eq RngIntElt then
        error "LocalRank did not return an int.";
    end if;

    // test the ranks with a known torus.
    K := NumberField(Polynomial([1, 0, 1]));
    torus := AlgebraicTorus(Rationals(), Rationals(), K);
    if not LocalRank(torus, 3) eq 0 then
        print("at 3");
        print(LocalRank(torus, 3));
        error "Local Rank of a well-known torus is wrong.";
    end if;
    if not LocalRank(torus, 17) eq 1 then
        print("at 17");
        print(LocalRank(torus, 17));
        error "Local Rank of a well-known torus is wrong.";
    end if;
    if not LocalRank(torus, Infinity()) eq 0 then
        print("at Infinity()");
        print(LocalRank(torus, Infinity()));
        error "Local Rank of a well-known torus is wrong.";
    end if;
    // LocalRank should have cached the ranks
    assert assigned torus`irreducibles[1]`ranks;
    assert IsDefined(torus`irreducibles[1]`ranks, Decomposition(BaseField(torus), 3)[1][1]);
    assert torus`irreducibles[1]`ranks[Decomposition(BaseField(torus), 3)[1][1]] eq 0;

    // global ranks should also have been cached
    assert assigned torus`irreducibles[1]`globalRank;
    assert GlobalRank(torus) eq 0;

    // test local rank for irreducible torus.
    res := LocalRank(torus`irreducibles[1], 17);
    assert torus1 ne torus;
end procedure;

procedure create_EtaleAlgebra()
    K := NumberField(Polynomial([1, 0, 1]));
    R<x> := PolynomialRing(K);
    F := NumberField(x^3 - 2);

    // the trivial algebra
    res := EtaleAlgebra([], K);
    assert Dimension(res) eq 0;

    // check the basic constructor
    res := EtaleAlgebra([F, K]);
    assert Dimension(res) eq 4;
    // check the basic constructor with defined basefield
    res := EtaleAlgebra([F, K], K);
    assert Dimension(res) eq 4;
    assert BaseField(res) eq K;
    // check the redefinition to a smaller field
    redef, res_to_redef := RedefineOverNewField(res, Rationals());
    // check the basic constructor with defined basefield Rationals()
    res := EtaleAlgebra([F, K], Rationals());
    assert Dimension(res) eq 8;
    assert AbsoluteDegree(BaseField(res)) eq 1;
    // get the standard realization of res
    realization, res_to_real := StandardRealization(res : update_realization:=true);
    assert IsRealized(res);
    assert Inverse(res_to_real)(res_to_real(res ! (3 / 12))) eq res ! (3 / 12);
    // check the redefinition over another field.
    redef, res_to_redef := RedefineOverNewField(res, K);
    assert not IsRealized(redef);
    assert redef ! K.1 eq res_to_redef(res ! [K.1,K.1]);
    assert Inverse(res_to_redef)(redef ! K.1) eq res ! [K.1,K.1];


    // check the constructor from a realized AlgMat
    QQ := TrivialInvolutiveRing(Rationals());
    M := MatrixAlgebra(QQ,2);
    x := M![0,-1,1,0];
    y := M![2,-3,3,2];
    N := sub<M | x, y>;
    N := InvolutiveAlgebra(N, map<N -> N | x :-> Transpose(x)>);
    M2 := MatrixAlgebra(Rationals(), 2);
    x2 := M2![0,4, 2,0];
    y2 := M2![4,0, 0,4];
    N2 := sub<M2 | x2, y2>;
    N2 := InvolutiveAlgebra(N2, [Basis(N2)[1], -Basis(N2)[2]]);
    A := InvolutiveDirectSum(N, N2);
    pre_skew, A_to_preskew := EtaleAlgebra(A);
    assert IsInvolutive(pre_skew);

    skew := RandomUnimodularMatrix(4, 4);
    skew := MatrixAlgebra(Rationals(), 4) ! skew;
    A := MatrixAlgebra<Rationals(), 4 | [skew * el * skew^(-1) : el in Basis(A)]>;
    algebra, A_to_alg, involution := EtaleAlgebra(A);
    assert Dimension(algebra) eq 4;
    assert Inverse(A_to_alg)(A_to_alg(Basis(A)[1])) eq Basis(A)[1];
    assert AbsoluteDegree(BaseField(algebra)) eq 1;
    assert involution eq false;

    alg2 := EtaleAlgebra([NumberField(Polynomial([1, 0, 1])),
                                      NumberField(Polynomial([-2, 0, 1]))]);
    is_iso, phi := IsIsomorphic(algebra, alg2);
    assert is_iso;
    assert phi(algebra ! 3) eq alg2 ! 3;
    assert Inverse(phi)(phi(algebra ! -12)) eq algebra ! -12;
    assert IsRealized(algebra);

    real, alg_to_real := RealizingAlgebra(algebra);
    assert real eq A;
    assert alg_to_real(Inverse(alg_to_real)(Basis(A)[1])) eq Basis(A)[1];

    // test redefinition with involution
    base := TrivialInvolutiveRing(QuadraticField(7));
    assert IsInvolutive(base);
    M := MatrixAlgebra(base,2);
    x := M![0,-1,1,0];
    y := M![2,-3,3,2];
    N := sub<M | x, y>;
    N := InvolutiveAlgebra(N, map<N -> N | x :-> Transpose(x)>);
    M2 := MatrixAlgebra(base, 2);
    x2 := M2![0,4, 2,0];
    y2 := M2![4,0, 0,4];
    N2 := sub<M2 | x2, y2>;
    N2 := InvolutiveAlgebra(N2, [Basis(N2)[1], -Basis(N2)[2]]);
    A := InvolutiveDirectSum(N, N2);
    pre_skew, A_to_preskew := EtaleAlgebra(A);
    assert IsInvolutive(pre_skew);
    redef := RedefineOverNewField(pre_skew, Rationals());
    assert IsInvolutive(redef);
    assert Dimension(redef) eq 2 * Dimension(pre_skew);
end procedure;

procedure run_DirectSum_AlgEta()
    K := NumberField(Polynomial([1, 0, 1]));
    R<x> := PolynomialRing(K);
    F := NumberField(x^3 - 2);

    alg1 := EtaleAlgebra([F, K]);
    assert Dimension(alg1) eq 4;
    alg2 := EtaleAlgebra([K, K], Rationals());
    assert Dimension(alg2) eq 4;
    // check the different version of DirectSum
    alg3 := DirectSum(alg1, alg2 : strict_base_field:=false);
    assert Dimension(alg3) eq 12;
    assert AbsoluteDegree(BaseField(alg3)) eq 1;
    alg4 := DirectSum(alg2, alg2);
    assert Dimension(alg4) eq 8;
    alg5 := DirectSum([alg1, alg2, alg3] : strict_base_field:=false);
    assert Dimension(alg5) eq 24;
end procedure;

procedure test_AlgEtaElt()
    K := NumberField(Polynomial([1, 0, 1]));
    R<x> := PolynomialRing(K);
    F := NumberField(x^3 - 2);

    alg1 := EtaleAlgebra([F, K]);
    one_in_alg1 := alg1 ! 1;
    fraction_in_alg1 := alg1 ! (4 / 7);
    element_of_K_in_alg1 := alg1 ! K.1;
    nontrivial_entry_in_alg1 := alg1 ! [F.1, K.1];
    assert alg1 ! 2 + alg1 ! K.1 eq alg1 ! (K.1 + 2);
    assert one_in_alg1 in alg1;
    
    // test this for the case where a field is not defined directly over the baseField
    alg1 := EtaleAlgebra([F, K], Rationals());
    one_in_alg1 := alg1 ! 1;
    fraction_in_alg1 := alg1 ! (4 / 7);
    K_abs := AbsoluteField(K);
    F_abs := AbsoluteField(F);
    nontrivial_entry_in_alg1 := alg1 ! [F_abs.1, K_abs.1];
    assert nontrivial_entry_in_alg1 + nontrivial_entry_in_alg1 eq 2 * nontrivial_entry_in_alg1;
    assert one_in_alg1 in alg1;
    assert K eq K_abs;
    tmp := alg1 ! [F.1, K.1];
    assert MinimalPolynomial(Eltseq(tmp)[1]) eq MinimalPolynomial(F.1);
    assert #Basis(alg1) eq Dimension(alg1);
    f := MinimalPolynomial(tmp);
    assert Degree(f) le Dimension(alg1);

    // test that some elements are not coercible
    is_coercible, tmp := IsCoercible(alg1, QNF());
    assert not is_coercible;
    assert tmp eq "Coercion is not implemented or impossible. Got FldNum";
end procedure;

procedure test_AlgEtaInv()
    K := NumberField(Polynomial([1, 0, 1]));
    R<x> := PolynomialRing(K);
    F := NumberField(x^2 - 3);

    alg := EtaleAlgebra([F, K, K], K);
    image_of_f1 := [- F.1, 0, 0];
    image_of_k1 := [0, 0, K.1];
    image_of_k2 := [0, K.1, 0];
    images := [*image_of_f1, image_of_k1, image_of_k2*];
    alg := InvolutiveAlgebra(alg, images, K.1);
    assert IsInvolutive(alg);

    // test again, but define everything over the rationals instead
    alg := EtaleAlgebra([F, K, K], Rationals());
    image_of_f1 := [- F.1, 0, 0];
    image_of_k1 := [0, 0, K.1];
    image_of_k2 := [0, K.1, 0];
    images := [image_of_f1, image_of_k1, image_of_k2];
    worked := false;
    // this does not work because F is defined over a field larger the Rationals()
    // so the involution cannot be set.
    try
        alg := InvolutiveAlgebra(alg, images, Rationals() ! 1);
    catch e
        worked := true;
    end try;

    assert worked;
    assert not IsInvolutive(alg);
end procedure;

procedure test_su_of_involution()
    K<k> := NumberField(Polynomial([1, 0, 1]));
    R<x> := PolynomialRing(K);
    F<f> := ext<K | x^2 - 3>;
    G<g> := ext<K | x^2 - 5>;

    alg := EtaleAlgebra([F, G, G], K);
    image_of_f1 := [- F.1, 0, 0];
    image_of_k1 := [0, 0, G.1];
    image_of_k2 := [0, G.1, 0];
    images := [*image_of_f1, image_of_k1, image_of_k2*];
    alg := InvolutiveAlgebra(alg, images, -K.1);
    assert IsInvolutive(alg);

    su := SUOfInvolutiveEtaleAlgebra(alg);
    print(su);
end procedure;

procedure test_TraceForm_on_AlgEtaInv()
    K := NumberField(Polynomial([1, 0, 1]));
    R<x> := PolynomialRing(K);
    F := NumberField(x^2 - 3);

    alg := EtaleAlgebra([F, K, K]);
    assert BaseField(alg) eq K;
    image_of_f1 := [- F.1, 0, 0];
    image_of_k1 := [0, 0, K.1];
    image_of_k2 := [0, K.1, 0];
    images := [*image_of_f1, image_of_k1, image_of_k2*];
    alg := InvolutiveAlgebra(alg, images, K.1);
    assert IsInvolutive(alg);

    // get an element of this algebra
    x := alg ! [2 * F.1, K.1, -K.1];
    res := Trace(x);
    assert res in BaseField(alg);

    B := TwistedTraceForm(x);
    assert Epsilonness(B) eq -1;
    // this is a form, so we should be able
    // to make an involution out of it
    N := InvolutiveAlgebra(B);
    assert IsInvolutive(N);

    // we should also be able to get the twisted left-reg of alg.
    M, M_nL, alg_to_M := InvolutiveLeftRegularEmbedding(alg, x : update_realization:=true);
    assert IsInvolutive(M);
    assert IsRealized(alg);
    assert RealizingAlgebra(alg) eq M;
    assert alg eq Domain(alg_to_M);
    assert M eq Codomain(alg_to_M);
    assert M_nL eq Generic(M_nL);
    assert Inverse(alg_to_M)(alg_to_M(alg ! 1)) eq alg ! 1;
end procedure;

procedure test_Rng_inv_extension()
    // trivial ring:
    Z := Integers();
    Z := TrivialInvolutiveRing(Z);
    assert IsInvolutive(Z);

    // numberfields
    F := NumberField(Polynomial([1, 0, 1]));
    F := InvolutiveRing(-F.1);
    assert assigned F`involution;
    assert _Conjugate(2 * F.1 + 3) eq -2 * F.1 + 3;
    F := InvolutiveRing(F, -F.1);
    assert assigned F`involution;
    assert _Conjugate(2 * F.1 + 3) eq -2 * F.1 + 3;
    assert Kind(F) eq 2;

    // finite fields
    K := InvolutiveRing(GF(5^4));
    assert assigned K`involution;
    assert _Conjugate(K.1) eq K.1^25;

    // complex field
    CC := InvolutiveRing(ComplexField(20));
    assert assigned CC`involution;
    assert _Conjugate(CC ! [3, 1]) eq CC ! [3, -1];

    // general ring
    R<x> := PolynomialRing(Integers());
    inv := hom<R -> R | -x>;
    R := InvolutiveRing(R, inv);
    assert assigned R`involution;
    assert _Conjugate(x) eq -x;
    assert Kind(R) eq 2;

    // general ring, but with trivial involution
    R<x> := PolynomialRing(Integers());
    inv := hom<R -> R | x>;
    R := InvolutiveRing(R, inv);
    assert assigned R`involution;
    assert _Conjugate(x) eq x;
    assert Kind(R) eq 1;

    // test a hand-written map which can be checked
    // finite field
    L := GF(3^6);
    L := InvolutiveRing(L, map<L -> L | x :-> Frobenius(x, 3)>);
    assert IsInvolutive(L);
    assert Kind(L) eq 2;

    // number field
    M := ext<F | Polynomial([-2, 0, 1])>;
    M := InvolutiveRing(M, hom<M -> M | - M.1>);
    assert IsInvolutive(M);
    assert Kind(M) eq 2;

    // test Epsilonness
    assert Epsilonness(M.1) eq -1;
    assert Epsilonness(M ! 1) eq 1;
    assert Epsilonness(M ! 1 + M.1) eq 0;
end procedure;

procedure test_known_CSA()
    A := AssociativeAlgebra<Rationals(), 2 |
        [
            [
                [1,0], [0,0]
            ],
            [
                [0,0], [0,1]
            ]
        ]>;
    assert not KnownCSA(A);

    M := MatrixAlgebra<Rationals(), 2 | [0,-1, 1,0]>;
    assert not KnownCSA(M);

    N := MatrixAlgebra(Rationals(), 3);
    assert KnownCSA(N);
end procedure;

procedure test_Alg_inv_extension()
    // The algebra DirectSum(Z+Z)
    A := AssociativeAlgebra<Integers(), 2 |
        [
            [
                [1,0], [0,0]
            ],
            [
                [0,0], [0,1]
            ]
        ]>;
    inv := map<A -> A | x :-> [Eltseq(x)[2], Eltseq(x)[1]]>;
    A := InvolutiveAlgebra(A, inv);
    assert IsInvolutive(A);
    assert _Conjugate(Basis(A)[1]) eq Basis(A)[2];
    assert Kind(A) eq 1;
    B := InvolutiveDirectSum(A, A);
    assert IsInvolutive(B);
    assert _Conjugate(Basis(B)[3]) eq Basis(B)[4];
    // Test Epsilonness on AlgAss
    assert Epsilonness(A ! [1, 1]) eq 1;
    assert Epsilonness(A ! [1, -1]) eq -1;
    assert Epsilonness(A ! [1, 0]) eq 0;

    Q := Rationals();
    Q := TrivialInvolutiveRing(Q);
    M := MatrixAlgebra(Q, 2);
    inv := map<M -> M | x :-> Transpose(x)>;
    M := InvolutiveAlgebra(M, inv);
    assert IsInvolutive(M);
    assert Kind(M) eq 1;

    // test with a nontrivial base involution
    F := QuadraticField(-1);
    N := MatrixAlgebra(InvolutiveRing(-F.1), 2);
    inv := map<N -> N |
        x :-> N ! [_Conjugate(Eltseq(Transpose(x))[i]) : i in [1..4]]>;
    N := InvolutiveAlgebra(N, inv);
    assert IsInvolutive(N);
    assert _Conjugate(Basis(N)[1] * F.1) eq - Basis(N)[1] * F.1;
    assert Kind(N) eq 2;

    // test the constructor taking images of basis elements
    K := InvolutiveRing(-F.1);
    // The algebra Q(i)(sqrt(2))
    B := AssociativeAlgebra<K, 2 |
        [
            [
                [1,0], [0,1]
            ],
            [
                [0,1], [2,0]
            ]
        ]>;
    // involutive with the nontrivial aut on Q(i)(sqrt(2)) | Q(i)
    B := InvolutiveAlgebra(B, [Basis(B)[1], -Basis(B)[2]]);
    assert IsInvolutive(B);
    assert _Conjugate(Basis(B)[1]) eq Basis(B)[1];
    assert _Conjugate(Basis(B)[2]) eq -Basis(B)[2];
    x := B ! [F.1, 0];
    assert _Conjugate(x) eq -x;
    assert Kind(B) eq 2;
    // test Epsilonness
    assert Epsilonness(Basis(B)[1]) eq 1;
    assert Epsilonness(Basis(B)[2]) eq -1;
    assert Epsilonness(Basis(B)[1] + Basis(B)[2]) eq 0;
end procedure;

procedure test_get_form_of_involution()
    // test with a simple involution and over a Field
    F := QuadraticField(-1);
    N := MatrixAlgebra(InvolutiveRing(-F.1), 2);
    inv := map<N -> N |
        x :-> N ! [_Conjugate(Eltseq(Transpose(x))[i]) : i in [1..4]]>;
    N := InvolutiveAlgebra(N, inv);
    q := GetFormOfInvolution(N);
    // the result must be a hermitian form
    assert _Conjugate(q) eq q;
    factor := q[1][1];
    assert q eq N ! [factor,0,0,factor];

    // test with a simple involution over a Skewfield
    K := QuadraticField(3);
    // use the nontrivial involution on K
    K := InvolutiveRing(-K.1);
    quats := QuaternionAlgebra<K | -1, -1>;
    // add the simplest involution to the quaternions (i.e. the involution is that of Q(sqrt(3)))
    // note that this will only be used to determine the hermitianness of the form,
    // but nothing about the involution on M itself
    quats := InvolutiveAlgebra(quats, [Conjugate(el) : el in Basis(quats)]);
    M := MatrixAlgebra(quats, 2);
    // add a nontrivial involution on M
    inv_on_M := map<M -> M |
        x :-> M ! [_Conjugate(Eltseq(Transpose(x))[i]) : i in [1..4]]>;
    M := InvolutiveAlgebra(M, inv_on_M : involutive_base_ring:=K);
    assert IsInvolutive(M);
    assert _Conjugate(M ! K.1) eq M ! -K.1;
    assert _Conjugate(M ! quats ! 1) eq M ! quats ! 1;
    assert _Conjugate(M ! quats ! [K.1, 0, 0, 0]) eq M ! quats ! [- K.1, 0, 0, 0];
    assert _Conjugate(M ! quats ! [0, 1, 0, 0]) eq M ! quats ! [0, -1, 0, 0];
    assert _Conjugate(M ! quats ! [0, 1, K.1, 0]) eq M ! quats ! [0, -1, K.1, 0];

    q := GetFormOfInvolution(M);
    assert _Conjugate(M ! quats ! [0, 1, 0, 0]) eq M ! quats ! [0, -1, 0, 0];
    assert _Conjugate(q) eq q;

    invalg := InvolutiveAlgebra(q);
    assert _Conjugate(M ! quats ! [0, 1, 0, 0]) eq M ! quats ! [0, -1, 0, 0];

    for i in [1..2], j in [1..2] do
        for d in [1..4] do
            seq := [[(i eq k and j eq l and d eq e) select
                     1
                     else 0 : e in [1..4]]
                    : k in [1..2], l in [1..2]];
            x := invalg ! seq;
            y := M ! seq;
            assert _Conjugate(x) eq invalg ! _Conjugate(y);
        end for;
    end for;
end procedure;

procedure test_LocalRankOfSU()
    // test that it works in a more complicated case
    F := QuadraticField(-1);
    N := MatrixAlgebra(InvolutiveRing(-F.1), 2);
    inv := map<N -> N |
        x :-> N ! [_Conjugate(Eltseq(Transpose(x))[i]) : i in [1..4]]>;
    N := InvolutiveAlgebra(N, inv);
    ind := LocalRankOfSU(N, 3);
    ind := LocalRankOfSU(N, Infinity());

    // test a well known case
    Q := TrivialInvolutiveRing(Rationals());
    M := MatrixAlgebra(Q, 3);
    M := InvolutiveAlgebra(M, map<M -> M | x :-> Transpose(x) >);
    kind := Kind(M);
    type := TypeOfInvolutionOnNormalFormCSA(M);
    q := M ! [[0, 1, 0], [1, 0, 0], [0, 0, 1]];
    N := InvolutiveAlgebra(q);
    assert IsInvolutive(BaseRing(N));
    ind := LocalRankOfSU(N, 3);
    assert ind eq 1;
    ind := LocalRankOfSU(N, Infinity());
    assert ind eq 1;
end procedure;

procedure test_coordinates_in_basis()
    K := QuadraticField(3);
    K := InvolutiveRing(-K.1);
    quats := QuaternionAlgebra<K | -1, -1>;
    quats := InvolutiveAlgebra(quats, [Conjugate(el) : el in Basis(quats)]);

    B := random_eps_hermitian_form(quats, 3, 1);
    M := Parent(B);
    coords := coordinates_in_basis(B, Basis(M));
    assert B eq &+[(M ! coords[i]) * Basis(M)[i] : i in [1..Dimension(M)]];
end procedure;

procedure test_find_isomorphism_type()
    M := MatrixAlgebra<Rationals(), 2 | [1,0,0,1],[0,-1,1,0]>;
    K, M_to_K := find_isomorphism_type(M);
    res, _ := IsIsomorphic(K, QuadraticField(-1));
    assert res;
end procedure;

procedure test_torus_generators()
    // the ext-case, easy example
    K := QNF();
    R<x> := PolynomialRing(K);
    F := ext<K | Polynomial([1,1]) : DoLinearExtension:=true>;
    E := ext<F | x^2 + 1>;
    torus := AlgebraicTorus(K, F, E : Prime:=13);
    irred := torus`irreducibles[1];
    gen := ArbitraryGenerator(irred : set_of_places:=[Decomposition(K, 5)[1][1]]);
    assert gen in E;
    assert Norm(gen, F) in [1, -1];

    K := QNF(); // NumberField(Polynomial([1, 0, 1]));
    R<x> := PolynomialRing(K);
    // F := ext<K | Polynomial([1,1]) : DoLinearExtension:=true>;
    // E := ext<F | x^2 + 1>;
    F := NumberField(x^3 - 7);
    E := ext<F | x^2 + 1>;

    // the ext-case
    torus := AlgebraicTorus(K, F, E : Prime:=13);
    place_3 := Decomposition(K, 3)[1][1];
    decomp_in_ff := [el[1]
                     : el in Decomposition(AbsoluteField(F), Characteristic(ResidueClassField(place_3)))
                     | Extends(el[1], place_3)];
    num := 0;
    for p_ff in decomp_in_ff do
        decomp_in_ef := [el[1]
            : el in Decomposition(AbsoluteField(E), Characteristic(ResidueClassField(p_ff)))
            | Extends(el[1], p_ff)];
        if #decomp_in_ef ge 2 then
            num +:= 1;
        end if;
    end for;
    assert num eq LocalRank(torus, place_3);

    place_5 := Decomposition(K, 5)[1][1];
    decomp_in_ff := [el[1]
                     : el in Decomposition(AbsoluteField(F), Characteristic(ResidueClassField(place_5)))
                     | Extends(el[1], place_5)];
    num := 0;
    for p_ff in decomp_in_ff do
        decomp_in_ef := [el[1]
            : el in Decomposition(AbsoluteField(E), Characteristic(ResidueClassField(place_5)))
            | Extends(el[1], p_ff)];
        if #decomp_in_ef ge 2 then
            num +:= 1;
        end if;
    end for;
    tmp := LocalRank(torus, place_5);
    assert num eq tmp;


    irred := torus`irreducibles[1];
    gen := ArbitraryGenerator(irred);
    assert gen in E;
    // I would like to make more asserts here, but the result is not unique at all
    // so this is very difficul aside from trivial asserts like this one:
    assert Norm(gen, F) in [1, -1];

    // // the swap-case
    torus := AlgebraicTorus(K, F, F : Prime:=13);
    irred := torus`irreducibles[1];
    gen := ArbitraryGenerator(irred);
    assert gen in F;


    // a complicated torus
    K := NumberField(Polynomial([1, 0, 1]));
    R<x> := PolynomialRing(K);
    F := NumberField(x^3 - 2);
    E := ext<F | x^2 - 7>;
    torus := AlgebraicTorus(K, F, E);
    gen := ArbitraryGenerator(torus`irreducibles[2]);
    assert Norm(gen, F) eq 1;
end procedure;

procedure test_FullRealizingAlgebra()
    K := NumberField(Polynomial([1, 0, 1]));
    R<x> := PolynomialRing(K);
    F := NumberField(x^3 - 2);
    E := ext<F | x^2 - 7>;

    torus := AlgebraicTorus(K, F, E : Prime:=13);
    mat := FullRealizingAlgebra(torus);

    assert BaseRing(mat) eq K;
    // the realization of a complete normtorus is the complete field:
    assert Dimension(mat) eq Degree(E, K);
    assert IsIsomorphic(find_isomorphism_type(mat), E);
end procedure;

procedure script()
    // used to test out stuff in DEV - this is not a unit test proper

    K := QuadraticField(3);
    K := InvolutiveRing(-K.1);
    quats := QuaternionAlgebra<K | -1, -1>;
    quats := InvolutiveAlgebra(quats, [Conjugate(el) : el in Basis(quats)]);
    M := MatrixAlgebra(quats, 2);
    M := sub<M | M>;

    A, M_to_A, A_to_M := AssociativeAlgebraOfNormalFormCSA(M);
    DirectSumDecomposition(A);
end procedure;

procedure testall_primitive()
    print(">Do the precision cuts work properly?");
    test_precision_cuts();
    print(".Success.\n");

    print(">Does _choose_elements work properly?");
    test_choose_elements();
    print(".Success.\n");

    print(">Does coordinates_in_basis work properly?");
    test_coordinates_in_basis();
    print(".Success.\n");

    print(">Does find_isomorphism_type work properly?");
    test_find_isomorphism_type();
    print(".Success.\n");

    print(">Does cast_from_RngPad_to_RngLocA work without error?");
    run_RngPad_cast();
    print(".Success.\n");
end procedure;

procedure testall_involution()
    print(">Do involutive rings work properly?");
    test_Rng_inv_extension();
    print(".Success.\n");

    print(">Do involutive associative Algebras work properly?");
    test_Alg_inv_extension();
    print(".Success.\n");

    print(">Does known_csa work properly?");
    test_known_CSA();
    print(".Success.\n");

    print(">Does GetFormOfInvolution work properly?");
    test_get_form_of_involution();
    print(".Success.\n");
end procedure;

procedure testall_characters()
    print(">Does ranks_of_irreds_at_prime_ext work without error?");
    run_ranks_of_irreds_at_prime_ext();
    print(".Success.\n");

    print(">Does ranks_of_irreds_at_prime_swap work without error?");
    run_ranks_of_irreds_at_prime_swap();
    print(".Success.\n");

    print(">Does ranks_of_irreds_at_infinity_ext work without error?");
    run_ranks_of_irreds_at_infinity_ext();
    print(".Success.\n");

    print(">Does ranks_of_irreds_at_infinity_swap work without error?");
    run_ranks_of_irreds_at_infinity_swap();
    print(".Success.\n");

    print(">Does ranks_of_irreds work without error?");
    run_ranks_of_irreds();
    print(".Success.\n");
end procedure;

procedure testall_etaalg()
    print(">Can I construct an EtaleAlgebra using all constructors?");
    create_EtaleAlgebra();
    print(".Success.\n");

    print(">Does DirectSum(AlgEta) work properly?");
    run_DirectSum_AlgEta();
    print(".Success.\n");

    print(">Can I work with AlgEtaElt's?");
    test_AlgEtaElt();
    print(".Success.\n");

    print(">Can I work with AlgEtaInv's?");
    test_AlgEtaInv();
    print(".Success.\n");

    print(">Can I convert AlgEtaInv to AlgTor?");
    test_su_of_involution();
    print(".Success.\n");

    print(">Can I get the traceform on an etale algebra?");
    test_TraceForm_on_AlgEtaInv();
    print(".Success.\n");

    print(">Does LocalRankOfSU work properly?");
    test_LocalRankOfSU();
    print(".Success.\n");
end procedure;

procedure testall_algtor()
//     print(">Can I construct an Algebraic Torus Irred using all constructors?");
//     construct_AlgebraicTorusIrred();
//     print(".Success.\n");
// 
//     print(">Can I construct an AlgebraicTorus with all constructors?");
//     construct_AlgebraicTorus();
//     print(".Success.\n");
// 
//     print(">Does IsIsomorphic work properly?");
//     run_IsIsomorphic();
//     print(".Success.\n");
// 
//     print(">Does DirectProduct work properly?");
//     run_DirectProduct();
//     print(".Success.\n");
// 
//     print(">Does WeilRestriction work properly?");
//     run_WeilRestriction();
//     print(".Success.\n");
// 
//     print(">Does LocalRank work properly?");
//     rank_of_torus();
//     print(".Success.\n");

    print(">Can I successfully calculate generators?");
    test_torus_generators();
    print(".Success.\n");

    print(">Does FullRealizingAlgebra work properly?");
    test_FullRealizingAlgebra();
    print(".Success.\n");
end procedure;

procedure run_all_unit_tests()
    // testall_primitive();
    // testall_involution();
    // testall_characters();
    // testall_etaalg();
    testall_algtor();
end procedure;
