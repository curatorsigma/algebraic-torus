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
