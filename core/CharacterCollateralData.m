declare type CharCollDat;
declare attributes CharCollDat :
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
    roots;

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
        galoisGroupOverQ::GrpPerm,
        galoisGroupOverBaseField::GrpPerm,
        galoisGroupOverExtensionField::GrpPerm,
        characterQuotientHom::Map,
        actionDescent::Map,
        roots::SeqEnum) -> CharCollDat
    {Constructor and input validation}
    require galoisGroupOverBaseField subset galoisGroupOverQ : "group to base_field must be subgroup of group to Q";
    require galoisGroupOverExtensionField subset galoisGroupOverBaseField : "group to extension_field must be subgroup of group to base_field";

    res := New(CharCollDat);
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
        : Ehat:=NormalClosure(AbsoluteField(Parent(e)))) -> FldNumElt
    {Calculate xi(e).

    REQUIRES
        xi in Domain(col_dat`characterQuotientHom)
        e in extension_field
    OUTPUT
        xi(e) in NormalClosure(extension_field)}

    E := Parent(e);

    require xi in Domain(col_dat`characterQuotientHom) :
        "Character must be in the original X_EF";
    coefficients := Eltseq(xi);
    require forall{x : x in coefficients | IsCoercible(Integers(), x)} :
        "Characters must have integral coefficients to be applicable.";
    coefficients := [Integers() ! x : x in coefficients];
    auts_Ehat, _, iota_auts_Ehat := AutomorphismGroup(Ehat);

    // this is Q[Gal(Ehat | BF) / Gal(Ehat | E)]
    X_E := Parent(xi);
    roots := [el[1] : el in Roots(DefiningPolynomial(AbsoluteField(E)), Ehat)];

    base_chars_lifted := [];
    for i in [1..#coefficients] do
        // X_E.i is an element of Gal(Ehat | BF) / Gal(Ehat | E)
        // we now need it as an element of Gal(Ehat | QQ) that can act on e
        auts_moving_r1_to_r := [];

        for g in auts_Ehat do
            if iota_auts_Ehat(g)(roots[1]) eq roots[i] then
                Append(~auts_moving_r1_to_r, g);
            end if;
        end for;
        assert #auts_moving_r1_to_r eq #col_dat`galoisGroupOverExtensionField;
        Append(~base_chars_lifted, auts_moving_r1_to_r[1]);
    end for;

    e_in_ehat := Ehat ! &+[Eltseq(e)[i] * roots[1]^(i -1) : i in [1..Degree(AbsoluteField(E))]];
    res := Ehat ! &*[iota_auts_Ehat(base_chars_lifted[i])(e_in_ehat)^coefficients[i] : i in [1..Dimension(X_E)]];
    assert res in Ehat;
    return res;
end intrinsic;
