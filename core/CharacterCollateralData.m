import "primitives.m":
    relative_field_but_does_not_segfault
;

declare type CharCollDat;
declare attributes CharCollDat :
    // The field tower, called EF | FF | BF | Rationals()
    // where [EF : FF] in {1,2}
    baseField,
    fixedField,
    extensionField,

    // galois group over Q
    galoisGroupOverQ,
    // galois group over base_field
    galoisGroupOverBaseField,
    // galois group over extension_field (or fixed_field in the swap case)
    galoisGroupOverExtensionField,
    // quotient map X_EF -> X_S (or the trivial X_FF -> X_FF in the swap case)
    characterQuotientHom,
    // map Gal_EFhat_BF -> Action on Domain(char_quotient)
    actionDescent,
    // Roots of extension_field (or fixed_field in the swap case) on which Gal_EFhat_QQ acts naturally
    roots,

    /////////////////////////////////////////////////////
    // OPTIONAL. THESE MAY NEVER ASSUME TO BE ASSIGNED //
    /////////////////////////////////////////////////////
    // if assigned, the GaloisData returned while calculating galoosGroupOverQ
    galoisData,

    // Normal closure of AbsoluteField(extension_field), redefined over base_field
    extensionFieldNormalClosure,

    // the following two are coupled and must be set at the same time
    // roots of DefiningPolynomial(AbsoluteField(extension_field) | base_field) in extensionFieldNormalClosure
    extensionFieldRootsInNormalClosure,
    // the base characters of X_EF / X_FF lifted to Automorphisms of extensionFieldNormalClosure
    baseCharsLiftedToEhatAutomorphisms
;

intrinsic Print(x::CharCollDat)
    {Print for CharCollDat}
    "CharCollDat:";
    "galoisGroupOverQ:";
    x`galoisGroupOverQ;
    "galoisGroupOverBaseField:";
    x`galoisGroupOverBaseField;
    "galoisGroupOverExtensionField:";
    x`galoisGroupOverExtensionField;
    "Universe(roots)";
    Universe(x`roots);
end intrinsic;

intrinsic CharacterCollateralData(
        dumb_input_1::Tup,
        dumb_input_2::Tup,
        dumb_input_3::Tup
        ) -> CharCollDat
    {Constructor and input validation}

    // do dumb require statements to ensure that the input has the correct length
    require #dumb_input_1 eq 3 :
        "The first input must be a Tuple containing baseField, fixedField, extensionField";
    require #dumb_input_2 eq 3 :
        "The first input must be a Tuple containing galois groups over Q, baseField and extensionField";
    require #dumb_input_3 eq 3 :
        "The first input must be a Tuple containing the characterQuotientHom, the actionDescent and roots
on  which the galois groups act.";

    // exploding dumb inputs that only exist because magma does not allow functions with more
    // then six input in its signature
    baseField, fixedField, extensionField := Explode(dumb_input_1);
    galoisGroupOverQ, galoisGroupOverBaseField, galoisGroupOverExtensionField := Explode(dumb_input_2);
    characterQuotientHom, actionDescent, roots := Explode(dumb_input_3);

    // now do dumb type checks to ensure the function type is correct
    require ISA(Type(baseField), FldNum) :
        "the first element of the first tuple must be a numberfield (baseField)";
    require ISA(Type(fixedField), FldNum) :
        "the first element of the first tuple must be a numberfield (fixedField)";
    require ISA(Type(extensionField), FldNum) :
        "the first element of the first tuple must be a numberfield (extensionField)";
    if extensionField ne fixedField then
        require BaseField(extensionField) eq fixedField :
            "extensionField must be fixedField or a degree 2 extension over it";
        require Degree(extensionField, fixedField) eq 2 :
            "extensionField must be fixedField or a degree 2 extension over it";
    end if;
    require BaseField(fixedField) eq baseField :
        "fixedField must be defined over baseField";

    require ISA(Type(galoisGroupOverQ), GrpPerm) :
        "the first element of the first tuple must be a GrpPerm (galoisGroupOverQ)";
    require ISA(Type(galoisGroupOverBaseField), GrpPerm) :
        "the first element of the first tuple must be a GrpPerm (galoisGroupOverBaseField)";
    require ISA(Type(galoisGroupOverBaseField), GrpPerm) :
        "the first element of the first tuple must be a GrpPerm (galoisGroupOverBaseField)";

    require ISA(Type(characterQuotientHom), Map) :
        "the first element of the first tuple must be a Map (characterQuotientHom)";
    require ISA(Type(actionDescent), Map) :
        "the first element of the first tuple must be a Map (actionDescent)";
    require ISA(Type(roots), SeqEnum) :
        "the first element of the first tuple must be a SeqEnum (roots)";


    require galoisGroupOverBaseField subset galoisGroupOverQ :
        "group to base_field must be subgroup of group to Q";
    require galoisGroupOverExtensionField subset galoisGroupOverBaseField :
        "group to extension_field must be subgroup of group to base_field";

    res := New(CharCollDat);
    res`baseField := baseField;
    res`fixedField := fixedField;
    res`extensionField := extensionField;
    res`galoisGroupOverQ := galoisGroupOverQ;
    res`galoisGroupOverBaseField := galoisGroupOverBaseField;
    res`galoisGroupOverExtensionField := galoisGroupOverExtensionField;
    res`characterQuotientHom := characterQuotientHom;
    res`actionDescent := actionDescent;
    res`roots := roots;
    return res;
end intrinsic;

intrinsic _ApplyCharacter(
        xi::ModGrpElt,  e::FldNumElt, col_dat::CharCollDat
        : Ehat:=false) -> FldNumElt
    {Calculate xi(e).

    REQUIRES
        xi in Domain(col_dat`characterQuotientHom)
        e in extension_field
    OUTPUT
        xi(e) in NormalClosure(extension_field)}

    E := Parent(e);
    is_iso, E_to_extension_field := IsIsomorphic(E, col_dat`extensionField);
    E_over_BF := relative_field_but_does_not_segfault(col_dat`baseField, E);
    require is_iso:
        "Parent(e) must be isomorphic to col_dat`extensionField";

    require xi in Domain(col_dat`characterQuotientHom) :
        "Character must be in the original X_EF";
    coefficients := Eltseq(xi);
    require forall{x : x in coefficients | IsCoercible(Integers(), x)} :
        "Characters must have integral coefficients to be applicable.";
    coefficients := [Integers() ! x : x in coefficients];

    if not assigned col_dat`extensionFieldNormalClosure then
        if assigned col_dat`galoisData then
            Ehat := GaloisSplittingField(
                AbsoluteField(E) : Galois:=col_dat`galoisData);
            col_dat`extensionFieldNormalClosure := relative_field_but_does_not_segfault(
                col_dat`baseField,
                Ehat);
        else
            Ehat := NormalClosure(AbsoluteField(E));
            col_dat`extensionFieldNormalClosure := relative_field_but_does_not_segfault(
                col_dat`baseField,
                Ehat);
        end if;
    end if;


    if not assigned col_dat`extensionFieldRootsInNormalClosure then
        col_dat`extensionFieldRootsInNormalClosure := [
            el[1] : el in Roots(DefiningPolynomial(E_over_BF), col_dat`extensionFieldNormalClosure)
        ];
        auts_Ehat, _, iota_auts_Ehat := AutomorphismGroup(col_dat`extensionFieldNormalClosure);
        col_dat`baseCharsLiftedToEhatAutomorphisms := [];
        for i in [1..#coefficients] do
            // X_E.i is an element of Gal(Ehat | BF) / Gal(Ehat | E)
            // we now need it as an element of Gal(Ehat | QQ) that can act on e
            auts_moving_r1_to_r := [];

            for g in auts_Ehat do
                if iota_auts_Ehat(g)(col_dat`extensionFieldRootsInNormalClosure[1])
                        eq col_dat`extensionFieldRootsInNormalClosure[i] then
                    Append(~auts_moving_r1_to_r, g);
                end if;
            end for;
            assert #auts_moving_r1_to_r eq #col_dat`galoisGroupOverExtensionField;
            Append(~col_dat`baseCharsLiftedToEhatAutomorphisms, iota_auts_Ehat(auts_moving_r1_to_r[1]));
        end for;
    end if;

    // we need the embedding along the first root, because that embedding was used to calculate
    // the base character lifts
    e_in_ehat := col_dat`extensionFieldNormalClosure ! &+[
        Eltseq(E_over_BF ! e)[i] * col_dat`extensionFieldRootsInNormalClosure[1]^(i -1)
        : i in [1..Degree(E_over_BF)]
    ];
    res := col_dat`extensionFieldNormalClosure ! &*[
        col_dat`baseCharsLiftedToEhatAutomorphisms[i](e_in_ehat)^coefficients[i]
        : i in [1..Dimension(Parent(xi))]
    ];

    printf "input: %o, character: %o, applied: %o\n\n", e, xi, Eltseq(res);
    return res;
end intrinsic;
