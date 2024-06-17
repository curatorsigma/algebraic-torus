// Dealing with involutive Etale Algebra to 

import "../core/primitives.m":
    coordinates_in_basis_fld,
    relative_field_but_does_not_segfault,
    _apply_base_involution,
    calculate_fixed_field_raw;

import "EtaleAlgebra.m" :
    image_of_original_to_image_of_our,
    image_of_original_to_image_of_our_raw;

declare attributes AlgEta :
    // OPTIONAL: for Involutive Etale Algebras
    // functions are implemented in InvolutiveEtaleAlgebra.m
    // for each field in algebra, the image of field.1 as an Element of algebra
    imagesOfFieldGenerators,
    // The image of BaseField(algebra).1 under the involution
    // (for involutions of 2nd kind)
    imageOfBaseFieldGenerator;

function apply_base_conjugate_to_polynomial(f, iobg)
    // given a polynomial f and the image of the base generator iobg
    // return f^sigma where sigma is the involution
    // BaseField(Parent(f)).1 -> iobg
    assert Type(f) eq RngUPolElt;
    assert ISA(Type(iobg), FldNumElt);

    sigma := map<Parent(iobg) -> Parent(iobg) |
                 x :-> &+[Eltseq(x)[i] * iobg^(i-1) : i in [1..Degree(Parent(iobg))]]>;
    return Polynomial([sigma(Eltseq(f)[i]) : i in [1..Degree(f)+1]]);
end function;

intrinsic _Conjugate(x::AlgEtaElt) -> AlgEtaElt
    {return involution(x)
    
    INPUTS
        AlgEtaElt x belonging to an IsInvolutive Etale Algebra
    OUTPUTS
        AlgEtaElt involution(x) in the same AlgEta
    NOTES
        Guaranteed to work even if involution is not fully validated
        This is required for the constructor to work properly}

    require IsInvolutive(Parent(x)) :
        "The Parent algebra does not have a defined involution.";

    assert3 forall{i : i in [1..#Parent(x)`extensions] | Parent(x)`imagesOfFieldGenerators[i] in Parent(x)};

    current := Parent(x) ! 0;
    for i in [1..#x] do
        field := Parent(x)`extensions[i];
        x_at_this_field := Eltseq(x)[i];
        res := &+[_ConjugateInEtaleAlgebra(Parent(x), Eltseq(x_at_this_field)[j]) *
                       PowerRespectSubalgebra(Parent(x)`imagesOfFieldGenerators[i], j-1)
                       : j in [1..Degree(field)]];
        current +:= res;
    end for;
    return current;
end intrinsic;

/// Given
///  - a map on an AlgEta which is potentially an involution
/// LET
///  - A := Domain(inv) (which is asserted to be equal to Codomain(inv))
/// CALCULATE
///  - inv((A ! 1) * A`baseField.1), cast to A`baseField
/// NOTES
///  - this function exists because casting from the Algebra A to A`baseField
///    is not naively possible (we need to error check that this cast is possible)
function image_of_base_field_gen(inv)
    A := Domain(inv);
    assert A eq Codomain(inv);
    if Dimension(A) eq 0 then
        return A`baseField.1;
    end if;

    im := inv((A ! 1) * A`baseField.1);
    curr := Eltseq(im)[1];
    is_coercible, curr := IsCoercible(A`baseField, curr);
    assert is_coercible;
    for i in [2..#im] do
        new := Eltseq(im)[i];
        is_coercible, new := IsCoercible(A`baseField, new);
        assert is_coercible;
        assert new eq curr;
    end for;
    return curr;
end function;

intrinsic _ConjugateInEtaleAlgebra(A::AlgEta, x::FldNumElt) -> FldNumElt
    {Apply the involution of A to x * 1_A where x is in Basefield(A)}

    require IsSubfield(Parent(x), BaseField(A)) :
        "Element must be in the BaseField over which the involution is defined.";

    return &+[Eltseq(BaseField(A) ! x)[i] * A`imageOfBaseFieldGenerator^(i-1)
              : i in [1..Degree(BaseField(A))]];
end intrinsic;

/// calculate the fixed field of the involution on algebra
///
/// INPUTS
///  AlgEta which IsInvolutive
/// OUTPUTS
///  FldNum: a subfield of BaseField(algebra) on which the involution is trivial
function calculate_fixed_field_of_involution(algebra)

    if not Type(algebra) eq AlgEta then
        printf "Passed type %o.\n", Type(algebra);
        error "Involution must be AlgEta.";
    end if;
    if not IsInvolutive(algebra) then
        error "Can only calculate the fixed field of an involutive algebra.";
    end if;

    return calculate_fixed_field_raw(
        BaseField(algebra),
        algebra`imageOfBaseFieldGenerator);
end function;

/// check if the involution on algebra is actually an involution
///
/// INPUTS
///  AlgEta algebra which IsInvolutive
/// OUTPUTS
///  BoolElt (is an involution)
///  str (Reason it isn't if it isn't, empty otherwise)
/// NOTES
///  Guaranteed to work even if the involution is not validated
///  This is required for the constructor to work properly
/// linearity over calculate_fixed_field_of_involution(algebra)
/// is assumed (lots of formulas use it)
/// and the involution is only represented with this in mind anyways
function check_involution(algebra)
    if not Type(algebra) eq AlgEta then
        printf "Passed type %o.\n", Type(algebra);
        error "Argument is not AlgEta.";
    end if;
    if not IsInvolutive(algebra) then
        error "Argument is not involutive.";
    end if;

    // check for idempotency
    for i in [1..#algebra`imagesOfFieldGenerators] do
        field_gen_in_alg := algebra ! [
            j eq i select algebra`extensions[i].1 else 0
            : j in [1..#algebra`imagesOfFieldGenerators]];
        if not _Conjugate(_Conjugate(field_gen_in_alg))
                eq field_gen_in_alg then
            return false, "Function is not Idempotent.";
        end if;
    end for;
    return true, "";
end function;

intrinsic Kind(algebra::AlgEta) -> RngIntElt
    {The Kind of the involution on algebra (i.E. 1 iff it is trivial on BaseField else 2)

    Note that algebra is usually not CSA, so naming this property
        kind is abuse of Notation.}
    require IsInvolutive(algebra) :
        "Algebra has no involution set.";
    return algebra`imageOfBaseFieldGenerator eq BaseField(algebra).1 select 1 else 2;
end intrinsic;

/// GIVEN
///     The image of the original field generator at im_index under the involution
///     The image of the base field generator under the involution
/// CALCULATE
///     The image of the new field generator at im_index under the same involution
/// In other words, calculate the transfer of the involution from the original to the new field
function transform_involution_to_our_fields(algebra, im, im_index, image_of_base_field_generator)
    is_iso, phi := IsIsomorphic(algebra`originalFields[im_index], algebra`extensions[im_index]);
    assert is_iso;
    // the index in which im has its nontrivial entry
    relevant_index := 0;
    while true do
        relevant_index +:= 1;
        if im[relevant_index] ne 0 then
            break;
        end if;
    end while;

    // this is the involution on the original field
    sigma := map<algebra`originalFields[im_index] -> algebra`originalFields[im_index] |
                 x :-> &+[
                _apply_base_involution(
                    Eltseq(x)[i] * im[relevant_index]^(i-1),
                    image_of_base_field_generator
                ) : i in [1..Degree(algebra`extensions[im_index])]]
                 >;
    // this applies the transferred involution in the new extension
    // original.1 -> im then induces the same involution as new.1 -> seq
    seq := [*
        (i eq relevant_index
            select algebra`extensions[i] ! phi(sigma(Inverse(phi)(algebra`extensions[im_index].1)))
            else algebra`extensions[i] ! 0)
        : i in [1..#im]
    *];
    assert forall{j : j in [1..#im] | Parent(seq[j]) eq algebra`extensions[j]};

    assert forall{j : j in [1..#seq] |
                  Evaluate(apply_base_conjugate_to_polynomial(
                    DefiningPolynomial(algebra`extensions[im_index]),
                    image_of_base_field_generator)
                            * Polynomial([0,1]),
                           seq[j]) eq 0};

    in_algebra := algebra ! seq;

    if GetAssertions() ge 2 then
        // recalculate image of base field generator in extension
        new_image := image_of_original_to_image_of_our_raw(
            Parent(image_of_base_field_generator),
            algebra`baseField,
            image_of_base_field_generator);
        new_image := algebra`baseField ! new_image;

        assert2 Evaluate(apply_base_conjugate_to_polynomial(
                    DefiningPolynomial(algebra`extensions[im_index]),
                    new_image) * Polynomial([0,1]),
                         in_algebra) eq algebra ! 0;
    end if;
    return in_algebra;
end function;

/// Internal only. Create an IsInvolutive AlgEta with the involution
/// defined by the images of field.1 for each field in algebra
///
/// The point of this function is to redefine the images into new fields
/// and then call the normal constructor again
function _involutive_algebra_from_field_elts(
            algebra, images_of_field_generators, image_of_base_field_generator)
    if not #algebra`extensions eq #images_of_field_generators then
        return false, "You must pass one image for each field in the algebra.", 0;
    end if;
    if not forall{x : x in images_of_field_generators | Type(x) in [SeqEnum, List]} then
        return false, "All generators must be given as a List or SeqEnum of FldNumElts", 0;
    end if;

    // this is a redirect to the version of the function giving the images of field generators
    // as AlgEtaElts
    // the difference is that for this function, the images are defined in the original fields
    // instead of algebra`extensions
    field_gens_in_algebra := [];
    for im_index in [1..#images_of_field_generators] do
        im := images_of_field_generators[im_index];
        if not forall{i : i in [1..#im] | IsCoercible(algebra`originalFields[i], im[i])} then
            return false, "You must specify the images of the field generators in the original fields.", 0;
        end if;
        if not forall{i : i in [1..#im] | IsSubfield(BaseField(algebra`originalFields[i]),
                                                      algebra`baseField)} then
            return false,
                "For an Involution to be well-defined, all fields in the algebra must have been defined over subfields of the baseField.", 0;
        end if;

        if not forall{j : j in [1..#im] |
                      Evaluate(apply_base_conjugate_to_polynomial(
                        DefiningPolynomial(algebra`originalFields[im_index]),
                        image_of_base_field_generator)
                                * Polynomial([0,1]),
                               algebra`originalFields[j] ! im[j]) eq 0} then
            return false, "All images of field generators need to satisfy the minimal polynomial twisted by the base involution.", 0;
        end if;

        image_in_our_fields := transform_involution_to_our_fields(
            algebra, im, im_index, image_of_base_field_generator);

        Append(~field_gens_in_algebra, image_in_our_fields);
    end for;

    return true, "", InvolutiveAlgebra(algebra, field_gens_in_algebra, image_of_base_field_generator);
end function;

intrinsic InvolutiveAlgebra(
        algebra::AlgEta,
        images_of_field_generators::List,
        image_of_base_field_generator::FldNumElt) -> AlgEta
    {Set the involution on algebra.

    INPUTS:
        AlgEta algebra
        List images_of_field_generators: either
            - List of elements of algebra
            - List of List/SeqEnum of FldNumElt, coercible into the algebra
            In either case, the ith entry defines the image of the ith field gen
            under the involution.
        FldNumElt image_of_base_field_generator: the image the baseField.1 in baseField}

    require #images_of_field_generators eq #algebra`extensions :
        "You must pass one image for each field in the algebra.";

    require Parent(image_of_base_field_generator) eq BaseField(algebra) :
        "The image of the base field generator must be given in the baseField.";
    require Evaluate(DefiningPolynomial(BaseField(algebra)), image_of_base_field_generator) eq 0 :
        "The image of the base field generator must have the same defining polynomial as BaseField().1";

    // first deal with the trivial case
    if #algebra`extensions eq 0 then
        algebra`imagesOfFieldGenerators := [algebra | ];
        algebra`imageOfBaseFieldGenerator := image_of_base_field_generator;
        return algebra;
    end if;

    // redirect the case where the images are defined in the original fields
    if ISA(Type(images_of_field_generators[1]), SeqEnum) or ISA(Type(images_of_field_generators[1]), List) then
        success, msg, res := _involutive_algebra_from_field_elts(
            algebra, images_of_field_generators, image_of_base_field_generator);
        require success : msg;
        return res;
    end if;

    for i in [1..#algebra`extensions] do
        require Evaluate(
                apply_base_conjugate_to_polynomial(
                    MinimalPolynomial(algebra`extensions[i].1) * Polynomial([0,1]),
                    image_of_base_field_generator),
                images_of_field_generators[i]) eq algebra ! 0:
            "An image of a field generator has a different MinimalPolynomial.";
    end for;

    // we are now in the case where elements are given in the algebra. require this.
    require algebra eq Parent(images_of_field_generators[1]) :
        "The images of field generators need to be in the algebra.";
    require forall{x : x in images_of_field_generators | Type(x) eq AlgEtaElt} :
        "All generators must be AlgEtaElts.";
    require forall{x : x in images_of_field_generators | Parent(x) eq algebra} :
        "All generators must be over the same algebra.";
    require IsIsomorphic(BaseField(algebra), Parent(image_of_base_field_generator)):
        "The image of the base field generator must be in a field isomorphic to the base field.";

    // validate the involution on the baseField
    // The User sets image_of_base_field_generator in some Field (call it P)
    // which is isomorphic to BaseField(algebra).
    // but we need it in BaseField(algebra) itself.
    // new_iobfg is chosen such that
    // the involution which maps P.1 -> image_of_base_field_generator BEFORE the isomorphism
    // maps BaseField(algebra).1 -> new_iobfg AFTER the isomorphism
    is_coercible, cast_iobfg := IsCoercible(
        BaseField(algebra), image_of_base_field_generator);
    assert is_coercible;
    gen_of_noncoerced_in_basefield := BaseField(algebra) ! Parent(image_of_base_field_generator).1;
    coords_of_bfg := coordinates_in_basis_fld(
        BaseField(algebra).1,
        [gen_of_noncoerced_in_basefield^(i-1)
         : i in [1..Degree(BaseField(algebra))]]);
    new_iobfg := &+[coords_of_bfg[i] * cast_iobfg^(i-1) : i in [1..Degree(BaseField(algebra))]];
    require &+[Eltseq(new_iobfg)[i] * new_iobfg^(i-1)
               : i in [1..Degree(BaseField(algebra))]]
            eq BaseField(algebra).1 :
        "The FldNumElt does not define an involution";

    // Assign the Involution to algebra
    // we are not done validating the input, but we need the object to work with it first.

    algebra`imagesOfFieldGenerators := [algebra | ];
    for i in [1..#algebra`extensions] do
        assert3 Parent(images_of_field_generators[i]) eq algebra;
        
        require Evaluate(
                apply_base_conjugate_to_polynomial(
                    MinimalPolynomial(algebra`extensions[i].1) * Polynomial([0,1]),
                    image_of_base_field_generator),
                images_of_field_generators[i]) eq algebra ! 0 :
            "The given image of the generator has a different MinimalPolynomial then the generator of this field, so it cannot define an involution.";
        Append(~algebra`imagesOfFieldGenerators, images_of_field_generators[i]);
    end for;

    assert ISA(Type(new_iobfg), FldNumElt);
    algebra`imageOfBaseFieldGenerator := new_iobfg;

    // check that involution is actually an involution
    success, msg := check_involution(algebra);
    if not success cmpeq true then
        // we need to unset the involution to leave algebra in a clean state
        delete algebra`imageOfBaseFieldGenerator;
        delete algebra`imagesOfFieldGenerators;
        require false : msg;
    end if;

    return algebra;
end intrinsic;

intrinsic InvolutiveAlgebra(
        algebra::AlgEta,
        images_of_field_generators::List,
        image_of_base_field_generator::FldRatElt) -> AlgEta
    {Trivial overload for the constructor when over Rationals().}

    require #images_of_field_generators eq #algebra`extensions :
        "You must pass one image for each field in the algebra.";
    base_field := BaseField(algebra);
    return InvolutiveAlgebra(algebra, images_of_field_generators, base_field ! 1);
end intrinsic;

intrinsic InvolutiveAlgebra(
        algebra::AlgEta,
        images_of_field_generators::List,
        image_of_base_field_generator::RngIntElt) -> AlgEta
    {Trivial overload for the constructor when over Rationals().}

    require #images_of_field_generators eq #algebra`extensions :
        "You must pass one image for each field in the algebra.";
    base_field := BaseField(algebra);
    return InvolutiveAlgebra(algebra, images_of_field_generators, base_field ! 1);
end intrinsic;

intrinsic InvolutiveAlgebra(alg::AlgEta,
        images_of_field_generators::SeqEnum,
        image_of_base_field_generator::Any) -> AlgEta
    {Trivial redirect to the List-case.}
    return InvolutiveAlgebra(
        alg, [*el : el in images_of_field_generators*], image_of_base_field_generator);
end intrinsic;

intrinsic InvolutiveAlgebra(
    algebra::AlgEta, inv::Map[AlgEta, AlgEta]) -> AlgEta
    {Redirect. Here, we are given an algebra and a map which is the involution}
    require Domain(inv) eq algebra :
        "The involution must have the algebra as Codomain.";
    require Codomain(inv) eq algebra :
        "The involution must have the algebra as Domain.";

    require forall{x : x in Basis(algebra) | inv(inv(x)) eq x} :
        "Involution must be idempotent.";

    iobfg := image_of_base_field_gen(inv);

    require forall{x : x in Basis(algebra) |
                   Evaluate(
                    apply_base_conjugate_to_polynomial(
                        MinimalPolynomial(inv(x)),
                        iobfg),
                    x) eq algebra ! 0} :
        "Involution must map each element to one with the same minimal polynomial.";


    images_of_field_generators := [inv(algebra !
        [(k eq i) select algebra`extensions[i].1 else 0
         : k in [1..#algebra`extensions]])
        : i in [1..#algebra`extensions]];

    return InvolutiveAlgebra(algebra, images_of_field_generators, iobfg);
end intrinsic;

intrinsic IsInvolutive(algebra::AlgEta) -> BoolElt
    {Does algebra have an involution set?}

    return assigned algebra`imagesOfFieldGenerators;
end intrinsic;

intrinsic NormalFormOfInvolution(algebra::AlgEta) -> List
    {For an involutive Algebra, calculate its normal form.

    The first output is a list of tuples, with the following meaning:
        <"Trivial", F, i> :
            Algebra contains the field F and the involution is trivial on it
            algebra`extensions[i] is equal to F
        <"Swap", F1, F2, phi, i1, i2> :
            algebra contains (up to isomorphism) the Summand F1+F2, phi:F1->F2 is an isomorphism
            and the involution maps F1 to F2 under phi and F2 to F1 under Inverse(phi)
            algebra`extensions[i1] is isomorphic to F1
            algebra`extensions[i2] is isomorphic to F2
        <"Extension", F, E, i> :
            Algebra contains the field E, F is a subfield of Degree 2
            and the involution is the nontrivial aut of E|F.
            algebra`extensions[i] is isomorphic to E
    The second output is a subfield of BaseField(algebra) which is the fixed field
    of BaseField(algebra) under the involution

    The fields F, F1, F2, E are defined over the second output.

    Note that the Trivial case is not possible when the fixed field is not equal
    to BaseField(algebra)
    }

    require IsInvolutive(algebra) :
        "Algebra must be involutive to calculate NormalFormOfInvolution.";

    global_fix := calculate_fixed_field_of_involution(algebra);
    if global_fix ne BaseField(algebra) then
        "have interesting global fix here";
        print(global_fix);
        print(BaseField(algebra));
    end if;

    normal_form := [**];
    normalized_indices := [];
    for field_index in [1..#algebra`extensions] do
        if field_index in normalized_indices then
            continue field_index;
        end if;
        tmp, index := ElementLiesInSubfield(algebra`imagesOfFieldGenerators[field_index]);
        if not tmp then
            error "Internal Error: image of field gen is not a field element.";
        end if;
        // since inv is an involution we know that
        //  the two fields at index and field_index are isomorphic
        // if the indices are equal, this is the extension or trivial type
        if index eq field_index then
            if global_fix eq BaseField(algebra) and
                    Eltseq(algebra`imagesOfFieldGenerators[field_index])[index]
                        eq algebra`extensions[index].1 then
                Append(~normal_form, <"Trivial", algebra`extensions[index], index>);
                Append(~normalized_indices, index);
                continue field_index;
            end if;

            // we are now in the "true" extension case:
            //  The involution acts on algebra`extensions
            //  it is fixed on global_fix

            fixed_field := calculate_fixed_field_raw(
                algebra`extensions[index],
                Eltseq(algebra`imagesOfFieldGenerators[index])[index] :
                iobfg := algebra`imageOfBaseFieldGenerator);

            // redefine fixed_field over global_fix
            fixed_field := relative_field_but_does_not_segfault(
                global_fix,
                fixed_field);
            // get the full field at this index as an extension of fixed_field
            extension_field := relative_field_but_does_not_segfault(
                fixed_field, algebra`extensions[index]);

            assert2 2 * AbsoluteDegree(fixed_field) eq AbsoluteDegree(extension_field);
            Append(~normal_form, <"Extension", fixed_field, extension_field, index>);
            Append(~normalized_indices, index);
            continue field_index;
        end if;

        // the two fields have different index. This is the (twisted) swap-case
        first_field := relative_field_but_does_not_segfault(
            global_fix, algebra`extensions[index]);
        second_field := relative_field_but_does_not_segfault(
            global_fix, algebra`extensions[field_index]);

        is_iso, phi := IsIsomorphic(
            first_field, second_field);
        assert is_iso;
        Append(~normal_form, <"Swap",
                              first_field,
                              second_field,
                              phi,
                              index,
                              field_index>);
        normalized_indices cat:= [index, field_index];
    end for;
    return normal_form, global_fix;
end intrinsic;

intrinsic SUOfInvolutiveEtaleAlgebra(algebra::AlgEta) -> AlgTor
    {Calculate SU(algebra, Involution(algebra))

     The result is AlgTor over the subfield of BaseField(algebra)
        fixed by Involution(algebra).}

    require IsInvolutive(algebra) :
        "Algebra must be involutive to calculate SU.";

    if IsRealized(algebra) then
        realization, alg_to_real := RealizingAlgebra(algebra);
        realizing_elements := [];
        central_idempotents := [];
    else
        realizing_elements := false;
        central_idempotents := false;
    end if;

    normal_form, global_fix := NormalFormOfInvolution(algebra);
    field_tower_list := [];
    for tup in normal_form do
        if tup[1] eq "Trivial" then
            // Trivial involutions have SU=1, ignore them for the torus
            continue tup;
        elif tup[1] eq "Swap" then
            // the twist is irrelevant for the SU. Ignore it and simply use one of the
            // two fields twice
            Append(~field_tower_list, <tup[2], tup[2]>);
            if IsRealized(algebra) then
                // for the realization, we actually care about both fields
                // because they may be realized differently
                new_realizer_1 := image_of_original_to_image_of_our_raw(
                    algebra`extensions[tup[5]],
                    tup[2],
                    algebra`realizingElements[tup[5]]);
                new_realizer_2 := image_of_original_to_image_of_our_raw(
                    algebra`extensions[tup[6]],
                    tup[3],
                    algebra`realizingElements[tup[6]]);
                Append(~realizing_elements, new_realizer_1 + new_realizer_2);

                Append(~central_idempotents,
                    algebra`centralIdempotents[tup[5]] + algebra`centralIdempotents[tup[6]]);
            end if;
        elif tup[1] eq "Extension" then
            Append(~field_tower_list, <tup[2], tup[3]>);
            if IsRealized(algebra) then
                new_realizer := image_of_original_to_image_of_our_raw(
                    algebra`extensions[tup[4]],
                    tup[3],
                    algebra`realizingElements[tup[4]]);
                Append(~realizing_elements, new_realizer);
                Append(~central_idempotents, algebra`centralIdempotents[tup[4]]);
            end if;
        end if;
    end for;

    // We now have the complete list of field towers and can simply create the AlgTor from it
    su := AlgebraicTorus(
        global_fix, field_tower_list :
        realizing_elements:=realizing_elements,
        central_idempotents:=central_idempotents);

    return su;
end intrinsic;

intrinsic Epsilonness(x::AlgEtaElt) -> RngIntElt
    {Calculate e such that x is e-hermitian in its involutive parent.

    OUTPUTS
        RngIntElt in \{-1,0,1\} : -1 or 1 if x is e-hermitian. 0 if it is neither.}

    require IsInvolutive(Parent(x)) :
        "Cannot determine Hermitianness in noninvolutive algebra.";
    conj := _Conjugate(x);
    if conj eq x then
        return 1;
    elif conj eq -x then
        return -1;
    else
        return 0;
    end if;
end intrinsic;

intrinsic Trace(x::AlgEtaElt) -> FldNumElt
    {Calculate the Trace of an element over the baseField.

    This is a redirect to the Trace already defined on numberfields.}
    assert3 forall{i : i in [1..#x] | Parent(Eltseq(x)[i]) eq Parent(x)`extensions[i]};

    return &+[Trace(Eltseq(x)[i], Parent(x)`baseField) : i in [1..#x]];
end intrinsic;

// From an Etale Algebra and a twist, create the involutive Algebra M_n(baseField)
intrinsic TwistedTraceForm(b::AlgEtaElt) -> AlgMatElt
    {Calculate the Form Trace(Conjugate(x) * b * y) on Parent(b).

    OUTPUTS
        AlgMatElt m: a matrix relative to Basis(Parent(b)) over Parent(b)`baseField
            that defines the traceform. i.e.
            Trace(Conjugate(x) * b * y) = x^dagger * m * y}

    alg := Parent(b);
    require IsInvolutive(alg) : "Algebra must be involutive.";

    // deal with the trivial case
    if #alg`extensions eq 0 then
        M := MatrixAlgebra(alg`baseField, 0);
        M := InvolutiveAlgebra(M, map<M -> M | x:-> x>);
        return M ! 1;
    end if;

    eps := Epsilonness(b);
    require eps in [1,-1] : "Twist must be hermitian or skew-hermitian.";

    basis := Basis(alg);
    entries := [];
    for i in [1..#basis] do
        Append(~entries, []);
        for j in [1..#basis] do
            form_ij := Trace(_Conjugate(basis[i]) * b * basis[j]);
            Append(~entries[i], form_ij);
        end for;
    end for;

    m := Matrix(entries);

    // now recast m in an involutive algebra
    // (the form is naturally in the involutive M_n(baseField).)
    N := sub<Parent(m) | Parent(m)>;
    field := BaseRing(N);
    assert field eq alg`baseField;
    field := InvolutiveRing(alg`imageOfBaseFieldGenerator);
    inv := map<N -> N |
               x :-> N ! [_Conjugate(Eltseq(Transpose(x))[i]) : i in [1..Dimension(N)]]>;
    N := InvolutiveAlgebra(N, inv);
    return N ! m;
end intrinsic;

intrinsic InvolutiveLeftRegularEmbedding(
        alg::AlgEta, b::AlgEtaElt
        : update_realization:=false) -> AlgMat, AlgMat, Map[AlgEta, AlgMat]
    {Construct the left-regular embedding alg -> M_n(baseField) with the involution
    defined by the Traceform twisted with b.

    This is a natural class of involutive embeddings by
        [Garibaldi, Rapinchuk. Weakly commensurable S-arithmetic groups. Prop 2.1]

    when update_realization is true, set the result as the realization of alg

    OUTPUTs
        The image of the embedding (i.e. isomorphic to alg)
            IsInvolutive() eq true, the involution from alg
        The generic M_n(L) into which alg was embedded
            IsInvolutive() eq true
        The invertible map alg -> embedding}

    require b in alg : "Twist must be in the algebra.";
    require IsInvolutive(alg) : "The algebra must be involutive.";

    eps := Epsilonness(b);
    require eps in [1,-1] : "Twist must be hermitian or skew-hermitian.";

    // calculate the realization (which is *sub* of M_n(baseField))
    real, alg_to_real := StandardRealization(
        alg :
        update_realization:=update_realization);

    // get the trace form as an element of real
    form := TwistedTraceForm(b);

    // make the realization involutive with the twisted form
    // *this is M_n* with the involution
    generic_of_real := InvolutiveAlgebra(form);
    assert IsInvolutivelyClosed(real, generic_of_real);
    real := InvolutiveAlgebra(
        real,
        map<real -> real |
            x :-> real ! _Conjugate(generic_of_real ! x)>);

    // and if required, update the realization into real
    if update_realization then
        alg`realizingElements := [
            real ! el : el in alg`realizingElements];
        alg`centralIdempotents := [
            real ! el : el in alg`centralIdempotents];
    end if;
    assert generic_of_real eq Generic(real);
    assert Domain(alg_to_real) eq alg;
    assert Codomain(alg_to_real) eq real;
    return real, generic_of_real, alg_to_real;
end intrinsic;
