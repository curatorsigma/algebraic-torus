// Random generators, mainly for fuzzing tests

function random_element(max_coefficient : basering:=Rationals(), nonzero:=true)
    while true do
        el := &+[Basis(basering)[i] * Random(-max_coefficient, max_coefficient)
                 : i in [1..Degree(basering)]];
        if (not nonzero) or (not el eq 0) then
            return el;
        end if;
    end while;
end function;

function random_irreducible_polynomial(max_coefficient, degree : basering:=Rationals())
    // I do not know of a good way to do this more efficiently :(
    while true do
        coeffs := [random_element(max_coefficient : basering:=basering) : i in [1..degree]];
        f := Polynomial(coeffs cat [1]);
        if IsIrreducible(f) then
            return f;
        end if;
    end while;
end function;

function random_numberfield(:
        basefield:=Rationals(),
        MAX_COEFFICIENT:=8,
        MIN_DEGREE:=1,
        MAX_DEGREE:=5)
    // Create a random numberfield
    //
    // INPUTS
    //  FldNum basefield: the Field to extend
    //  MAX_COEFFICIENT : The maximal coefficient to use for the defining polynomial
    //  MIN_DEGREE : the minimal degree over basefield
    //  MAX_DEGREE : the maximal degree over basefield
    
    degree := Random(MIN_DEGREE, MAX_DEGREE);
    f := random_irreducible_polynomial(MAX_COEFFICIENT, degree : basering:=basefield);
    if Degree(f) eq 1 then
        return ext<basefield | Polynomial([-1, 1]) : DoLinearExtension:=true>;
    end if;
    F := ext<basefield | f : DoLinearExtension:=true>;
    return F;
end function;

function random_set_of_places(field : 
        MIN_NUMBER_OF_FINITE_PLACES:=0,
        MAX_NUMBER_OF_FINITE_PLACES:=3,
        BASE_INDEX_OF_FINITE_PLACES:=10,
        MIN_NUMBER_OF_INFINITE_PLACES:=0,
        MAX_NUMBER_OF_INFINITE_PLACES:=2)
    // Create a random set of places
    //
    // INPUTS
    //  FldNum field: Numberfield to create places in
    //  MIN_NUMBER_OF_FINITE_PLACES: Minimal Number of finite places in set_of_places
    //  MAX_NUMBER_OF_FINITE_PLACES: Maximal Number of finite places in set_of_places
    //  BASE_INDEX_OF_FINITE_PLACES: The maximal Index of the chosen finite places prime in [2, 3, 5, ...\n]
    //      When all the places over the max base prime are already chosen, a place over a larger prime may be used
    //  MIN_NUMBER_OF_INFINITE_PLACES: Minimal Number of infinite places in set_of_places
    //  MAX_NUMBER_OF_INFINITE_PLACES: Maximal Number of infinite places in set_of_places

    field := AbsoluteField(field);
    // create random set of places
    set_of_places := [];
    // Finite Places
    number_of_finite_places := Random(MIN_NUMBER_OF_FINITE_PLACES, MAX_NUMBER_OF_FINITE_PLACES);
    for i in [1..number_of_finite_places] do
        // get a random prime and add it
        prime_index := Random(BASE_INDEX_OF_FINITE_PLACES);
        p := 2;
        for j in [1..prime_index] do
            p := NextPrime(p);
        end for;
        while true do
            decomp := Decomposition(field, p);
            index := Random(1, #decomp);
            if not decomp[index][1] in set_of_places then
                Append(~set_of_places, decomp[index][1]);
                break;
            end if;
            p := NextPrime(p);
        end while;
    end for;
    set_of_places := [el : el in set_of_places];

    // Infinite places
    all_infinite_places := InfinitePlaces(field);
    number_of_infinite_places := Random(MIN_NUMBER_OF_INFINITE_PLACES,
                                        Minimum(MAX_NUMBER_OF_INFINITE_PLACES, #all_infinite_places));
    for i in [1..number_of_infinite_places] do
        while true do
            index := Random(1, #all_infinite_places);
            inf_place := all_infinite_places[index];
            if inf_place in set_of_places then
                continue;
            end if;
            Append(~set_of_places, inf_place);
            break;
        end while;
    end for;
    return set_of_places;
end function;

function _generate_random_element(D)
    // Create one element of D at random
    if ISA(Type(D), Alg) then
        res := D ! 0;
        for i in [1..Dimension(D)] do
            a := _generate_random_element(BaseRing(D));
            res +:= (D ! a) * Basis(D)[i];
        end for;
        return res;
    end if;

    if Type(D) in [FldFin, RngIntRes] then
        return Random(D);
    end if;

    if Type(D) in [FldRat, RngPad, FldPad] or ISA(Type(D), FldNum) then
        return random_element(6 : basering:=D, nonzero:=false);
    end if;

    if Type(D) in [FldRe] then
        return D ! random_element(6 : basering:=Rationals(), nonzero:=false);
    end if;

    if Type(D) in [FldCom] then
        return D ! [random_element(6 : basering:=Rationals(), nonzero:=false) : i in [1..2]];
    end if;

    print(Type(D));
    error "This type has no known generator.";
end function;

function random_eps_hermitian_form(D, n, eps)
    // Create a random eps-hermitian form on D^n
    //
    // INPUTS
    //  Rng D : involutive Ring (or Algebra)
    //  RngIntElt n : dimension
    // OUTPUTS
    //  AlgMatElt B in M_n(D) which is eps-hermitian

    // There is no general way to create a random element of D
    // instead, choose a random Element from the Basis if D is Alg
    // or call a random generator if D is not an Algebra
    tmp := MatrixAlgebra(D, n);
    alg := sub<tmp | tmp>;
    alg := InvolutiveAlgebra(alg, [Transpose(x) : x in Basis(alg)]);
    res := alg ! 0;

    // fill strict upper triangle and mirror to bottom
    for i in [1..n] do
        for j in [i+1..n] do
            res[i][j] := _generate_random_element(D);
            res[j][i] := eps * _Conjugate(res[i][j]);
        end for;
    end for;

    // fill the diagonal: create a random element and symmetrize it
    // (Symd < Sym and Alt < Skew, both are still true in char=2)
    for i in [1..n] do
        a := _generate_random_element(D);
        res[i][i] := a + eps * _Conjugate(a);
    end for;
    return res;
end function;
