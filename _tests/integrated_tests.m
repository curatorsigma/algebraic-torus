// integrated tests for the AlgebraicTorus package

import "../s_ample_tori/s_ample_tori.m":
    find_S_ample_subtori;

import "random_generators.m" :
    random_set_of_places;

procedure create_torus_from_AlgEtaInv()
    K := NumberField(Polynomial([1, 0, 1]));
    R<x> := PolynomialRing(K);
    F := NumberField(x^2 - 3);

    alg := EtaleAlgebra([F, K, K], K);
    assert BaseField(alg) eq K;
    image_of_f1 := [- F.1, 0, 0];
    image_of_k1 := [0, 0, K.1];
    image_of_k2 := [0, K.1, 0];
    images := [image_of_f1, image_of_k1, image_of_k2];
    alg := InvolutiveAlgebra(alg, images, K.1);
    assert IsInvolutive(alg);
    torus := AlgebraicTorus(alg);
end procedure;

procedure test_find_s_ample()
    R<x> := PolynomialRing(Rationals());
    F := NumberField(x^3 - 7);
    E := ext<F | x^2 + 1>;
    alg := EtaleAlgebra([E], F);
    alg := InvolutiveAlgebra(alg, [*[-E.1]*], F.1);
    alg := RedefineOverNewField(alg, Rationals());
    twist := alg ! 1;
    set_of_places := [Infinity(), 3, 5];
    s_amples := find_S_ample_subtori(alg, twist, set_of_places);
    assert #s_amples eq 1;

    K := QuadraticField(-1);
    alg := EtaleAlgebra([K, K, K], Rationals());
    image_of_f1 := [- K.1, 0, 0];
    image_of_k1 := [0, 0, K.1];
    image_of_k2 := [0, K.1, 0];
    images := [*image_of_f1, image_of_k1, image_of_k2*];
    alg := InvolutiveAlgebra(alg, images, 1);
    assert IsInvolutive(alg);

    // get an element of this algebra
    twist := alg ! [2 * K.1, K.1, -K.1];

    bf := BaseField(alg);
    set_of_places := [InfinitePlaces(bf)[1], Decomposition(bf, 3)[1][1], Decomposition(bf, 7)[1][1]];
    s_amples := find_S_ample_subtori(alg, twist, set_of_places);
end procedure;

procedure run_all_integrated_tests()
    print(">Can I create a torus from AlgEtaInv?");
    create_torus_from_AlgEtaInv();
    print(".Success.\n");

    print(">Can I find s-ample tori?");
    test_find_s_ample();
    print(".Success.\n");
end procedure;
