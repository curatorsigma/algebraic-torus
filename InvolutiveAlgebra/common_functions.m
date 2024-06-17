// functions common to involutive algebras of any type

function add_base_involution_if_allowed(ring, trivial_base_inv_allowed, alg)
    if not trivial_base_inv_allowed then
        if not IsInvolutive(ring) then
            return alg, false, "Can only define involutions on Algebras over involutive rings.";
        end if;
    else
        if not IsInvolutive(ring) then
            // add the trivial involution if that is allowed and required
            // this only sets attributes of ring; no resetting of alg`ring required
            ring := InvolutiveRing(ring);
        end if;
    end if;
    return alg, true, "";
end function;

// Preliminary notes on some of the following functions:
// We allow an algebra to be a Star-Algebra over something that is not BaseRing(Algebra)
// as long as the involutive_base_ring is somewhere in BaseRing(...(BaseRing(Algebra))).
// This means that we often need to recursively go down the chain of BaseRing before we
// can check properties (because we only get linearity at involutive_base_ring).
// This is the reason most of these recursive functions exist and have to be recursive.


/// Find a basis of submod as an involutive_base_ring subalgebra
///
/// INPUTS
///  Alg submod
///  Rng involutive_base_ring : a Ring appearing somewhere in BaseRing^n(submod)
///  Map[Alg, Alg] embedding from submod into some parent superalgebra
/// OUTPUTS
///  SeqEnum[AlgElt] Basis of submod as an involutive_base_ring embedded in the superalgebra
function basis_to_involutive_base_ring(
        submod, involutive_base_ring : embedding:=map<submod -> submod | x :-> x>)

    if not ISA(Type(submod), Alg) then
        error "submod should be Alg. Internal error.";
    end if;
    // we are done recursing
    if BaseRing(submod) cmpeq involutive_base_ring then
        res := [embedding(b) : b in Basis(submod)];
        return res;
    end if;

    // we have to recurse deeper
    bases_rec := [];
    for b in Basis(submod) do
        // sub_submod is span(b) in submod as a BaseRing-Module
        // i.e. the sub-module, NOT actually the subalgebra
        sub_submod := BaseRing(submod);
        // the map from sub_submod into Domain(inv) (the parent-algebra)
        sub_embedding := map<sub_submod -> submod | x :-> (submod ! x) * b> * embedding;
        bases_rec cat:= basis_to_involutive_base_ring(
            sub_submod, involutive_base_ring : embedding:=sub_embedding);
    end for;
    return bases_rec;
end function;

/// Check whether inv is in fact an involution.
///
/// INPUTS
///  Map[Alg, Alg] inv
///  Rng involutive_base_ring : the ring over which Domain(inv) is supposed to be an involutive algebra
/// OUTPUTS
///  BoolElt passed all our tests?
///  str Errormessage if inv did not pass all tests
/// TESTS (a, b, c in Basis)
///  inv^2(a) eq a
///  inv(a + b) eq inv(a) + inv(b)
///  inv(a*b) eq inv(b) * inv(a)
function check_involution_on_Alg(inv, involutive_base_ring)
    alg := Domain(inv);

    basis := basis_to_involutive_base_ring(alg, involutive_base_ring);

    for a in basis do
        inva := inv(a);
        if not inv(inva) eq a then
            a;
            inva;
            inv(inva);
            return false, "Map is not idempotent on the basis.";
        end if;
        for b in basis do
            invb := inv(b);
            if not inv(a + b) eq inva + invb then
                return false, "Map is not additive on the basis.";
            end if;
            if not inv(a * b) eq invb * inva then
                "Failure:";
                a;
                b;
                inva;
                invb;
                inv(a * b);
                return false, "Map is not op-multiplicative on the basis.";
            end if;
        end for;
    end for;

    return true, "No tests are known for this Ring.";
end function;

/// Get the images of a involutive_base_ring-basis of submod under inv.
/// involutive_base_ring need not be BaseRing(submod), which is why this function exists
///
/// INPUTS
///  Map[Alg, Alg] inv
///  Alg submod: BaseRing(...(BaseRing(Codomain(inv))))
///  Map[submod -> Codomain(inv)] embedding
///  Rng involutive_base_ring : a BaseRing(...(BaseRing(Codomain(inv))))
///      over which Codomain(inv) is an involutive algebra
///      the recursion will stop at this level since involutive_base_ring has
///      its own known involution
/// OUTPUTS
///  List[...List[AlgElt]] : recursive lists as deep as the number of BaseRing calls to
///      get from submod to involutive_base_ring, containing elements of the Basis elements
///      in involutive_base_ring (branching once for each element of the Basis in each BaseRing step)
function get_images_of_basis_recurse(inv, submod, embedding,
                                     involutive_base_ring)
    if not ISA(Type(submod), Alg) then
        error "submod should be Alg. Internal error.";
    end if;
    // we are done recursing
    if BaseRing(submod) cmpeq involutive_base_ring then
        res := [*inv(embedding(b)) : b in Basis(submod)*];
        return res;
    end if;

    // we have to recurse deeper
    list_of_images := [**];
    for b in Basis(submod) do
        // sub_submod is span(b) in submod as a BaseRing-Module
        // i.e. the sub-module, NOT actually the subalgebra
        sub_submod := BaseRing(submod);
        // the map from sub_submod into Domain(inv) (the parent-algebra)
        sub_embedding := map<sub_submod -> submod | x :-> (submod ! x) * b> * embedding;
        Append(~list_of_images,
               get_images_of_basis_recurse(inv, sub_submod, sub_embedding,
                                           involutive_base_ring));
    end for;
    return list_of_images;
end function;

/// INPUTS
///  Map[Alg, Alg] inv
///  Alg submod: BaseRing(...(BaseRing(Codomain(inv))))
///  Map[submod -> Codomain(inv)] embedding
///  Rng involutive_base_ring : a BaseRing(...(BaseRing(Codomain(inv))))
///      over which Codomain(inv) is an involutive algebra
///      the recursion will stop at this level since involutive_base_ring has
///      its own known involution
/// OUTPUTS
///  BoolElt true iff the involution is trivial,
///      except perhaps an action on involutive_base_ring
function involution_is_trivial_to_base_ring(
        inv, submod, embedding, involutive_base_ring)
    if not ISA(Type(submod), Alg) then
        error "submod should be Alg. Internal error.";
    end if;
    // we are done recursing; return whether the involution is trivial here.
    if BaseRing(submod) cmpeq involutive_base_ring then
        for b in Basis(submod) do
            if not inv(embedding(b)) eq embedding(b) then
                return false;
            end if;
        end for;
        return true;
    end if;

    // we have to recurse deeper
    for b in Basis(submod) do
        // sub_embedding is span(b) in submod as a BaseRing-Module
        // i.e. the sub-module, NOT actually the subalgebra
        sub_submod := BaseRing(submod);
        // the map from sub_submod into Domain(inv) (the parent-algebra)
        sub_embedding := map<sub_submod -> submod | x :-> (submod ! x) * b> * embedding;
        is_trivial := involution_is_trivial_to_base_ring(
            inv, sub_submod, sub_embedding, involutive_base_ring);
        if not is_trivial then
            return false;
        end if;
    end for;
    return true;
end function;

/// Create the map alg -> alg defined by the images of the basis
///
/// INPUTS
///  Alg subalg : Some BaseRing(...(BaseRing(alg)))
///  Alg alg : the complete parent alg. images_of_basis has entries in alg, NOT subalg
///  [[...[AlgElt]]] images_of_basis: recursive list of lists of Algebra Elements
///      recursion depth must be the number of BaseRings between subalg and base_ring
///      e.g. if base_ring eq BaseRing(alg), images_of_basis must be [AlgElt]
///      with elements in alg and of length Dimension(subalg)
///  Rng base_ring : a ring somewhere in BaseRing(...BaseRing(subalg)). the map is assumed
///      to coincide with map_on_base on base_ring
///  str map_on_base:="Involution" :: if "Involution": map coincides with base_ring`involution
///                                   if "Trivial" : map is trivial on base_ring
/// OUTPUTS
///  map[Alg, Alg] the map the defined by these images of the basis and the map on base_ring
///      will be map<subalg -> alg>
///  BoolElt calculation could be completed successfully
///  str Errormessage if calculation could not be completed
function construct_map_from_images_of_basis(
        subalg, alg, images_of_basis, base_ring : map_on_base:="Involution")

    if not map_on_base in ["Involution", "Trivial"] then
        return 0, false, "map_on_base must be Involution or Trivial.";
        if map_on_base eq "Involution" and not IsInvolutive(base_ring) then
            return 0, false, "base_ring is not involutive, but I am supposed to use its involution.";
        end if;
    end if;

    if #images_of_basis eq 0 then
        return map<subalg -> alg | x :-> x>, true, "";
    end if;

    // we have reached the last recursion level
    if ISA(Type(images_of_basis[1]), RngElt) then
        if not Parent(images_of_basis[1]) cmpeq alg then
            return 0, false, "images_of_basis are not over the correct involutive ring.";
        end if;
        if not BaseRing(subalg) cmpeq base_ring then
            return 0, false, "Last recursion level has wrong BaseRing. (must be the set base_ring)";
        end if;

        // set the map on the base
        if map_on_base eq "Involution" then
            base_map := map<base_ring -> base_ring | x :-> _Conjugate(x)>;
        elif map_on_base eq "Trivial" then
            base_map := map<base_ring -> base_ring | x :-> x>;
        end if;
        if ISA(Type(alg), AlgMat) then
            res := map<subalg -> alg |
                       x :-> &+[(alg ! base_map(Coordinates(subalg, x)[i])) * images_of_basis[i]
                                : i in [1..Dimension(subalg)]]>;
        else
            res := map<subalg -> alg |
                       x :-> &+[base_map(Coordinates(subalg, x)[i]) * images_of_basis[i]
                                : i in [1..Dimension(subalg)]]>;
        end if;
        return res, true, "";
    end if;

    // there is more recursion depth to go through
    if not #images_of_basis eq Dimension(subalg) then
        "At level:";
        alg;
        "with base level:";
        base_ring;
        "images_of_basis";
        images_of_basis;
        return 0, false, "images_of_basis has wrong number of elements.";
    end if;

    recursive_maps := [];
    for i in [1..#images_of_basis] do
        map, success, msg := construct_map_from_images_of_basis(
            BaseRing(alg), alg, images_of_basis[i], base_ring : map_on_base:=map_on_base);
        if not success then
            return 0, false, "";
        end if;
        Append(~recursive_maps, map);
    end for;

    res := map<subalg -> alg |
               x :-> &+[recursive_maps[i](Coordinates(subalg, x)[i]) : i in [1..Dimension(subalg)]]>;
    return res, true, "";
end function;

/// basic constructors for all types of *-Alg are the same
/// but they do not have a direct inheritance structure, so
/// they call this function instead. requires are handled in the caller
///
/// INPUTS
///  Alg alg
///  Map[Alg, Alg] inv
///  BoolElt trivial_base_inv_allowed : 
///    automatically add the trivial involution if the basering has none
/// OUTPUTS
///  Alg The modified object
///  BoolElt did any problems occur?
///  str The Error message if problems occured
function involutive_algebra_constructor(alg, inv :
                                        involutive_base_ring:=BaseRing(alg),
                                        trivial_base_inv_allowed:=true)

    if not alg cmpeq Domain(inv) then
        return alg, false, "The involution must be given as a map from the given algebra.";
    end if;
    if not alg cmpeq Codomain(inv) then
        return alg, false, "The involution must be given as a map into the given algebra.";
    end if;
    if not IsInvolutive(involutive_base_ring) then
        return alg, false, "The Base ring must be involutive.";
    end if;

    // get the images of the generators and redirect
    images_of_basis := get_images_of_basis_recurse(
        inv, alg, map<alg -> alg | x :-> x>, involutive_base_ring);
    // this will currently call involutive_algebra_from_images_of_basis
    return InvolutiveAlgebra(
        alg, images_of_basis :
        involutive_base_ring:=involutive_base_ring,
        trivial_base_inv_allowed:=trivial_base_inv_allowed), true, "";
end function;

/// Common function adding an involution based on images of the basis elements.
function common_involutive_algebra_from_images(
        alg, images_of_basis, involutive_base_ring, trivial_base_inv_allowed)

    if not #images_of_basis eq Dimension(alg) then
        return 0, false, "Not the correct number of base images given.";
    end if;

    // deal with base involution
    alg, success, msg := add_base_involution_if_allowed(
        involutive_base_ring, trivial_base_inv_allowed, alg);
    if not success then
        return 0, false, msg;
    end if;

    inv, success, msg := construct_map_from_images_of_basis(
        alg, alg, images_of_basis, involutive_base_ring);
    if not success then
        return 0, false, msg;
    end if;

    success, msg := check_involution_on_Alg(inv, involutive_base_ring);
    if not success then
        return 0, false, msg;
    end if;

    alg`involution := inv;
    alg`involutiveBaseRing := involutive_base_ring;
    return alg, true, "";
end function;

/// Recursively applies the involution of involutive_base_ring
///
/// INPUTS
///  AlgElt x (in a BaseRing^n(alg))
///  Alg alg (the full parent algebra)
///  Rng involutive_base_ring : the ring over which alg is involutive
/// OUTPUTS
///  AlgElt in Parent(x) with the base involution applied
function base_conjugate_recurse(x, alg, involutive_base_ring)
    subalg := Parent(x);

    // we are done recursing. Return with applied base involution
    if BaseRing(subalg) cmpeq involutive_base_ring then
        res := subalg ! 0;
        for i in [1..Dimension(subalg)] do
            res +:= (subalg ! _Conjugate(Eltseq(x)[i])) * Basis(subalg)[i];
        end for;
        return res;
    end if;

    // the subalg is not yet directly defined over involutive_base_ring
    res := subalg ! 0;
    for i in [1..Dimension(subalg)] do
        res +:= (subalg ! base_conjugate_recurse(
            Eltseq(x)[i], alg, involutive_base_ring)) * Basis(subalg)[i];
    end for;
    return res;
end function;

function common_base_conjugate(x)
    // Inputs
    //  AlgElt x
    // OUTPUTS
    //  AlgElt : involution of the basering applied to every entry

    alg := Parent(x);
    involutive_base_ring := InvolutiveBaseRing(alg);
    return base_conjugate_recurse(x, alg, involutive_base_ring);
end function;

/// Is alg CSA?
/// WARNING: does not find all CSAs, but never returns false positives
///
/// INPUTS
///  Alg alg
/// OUPUTS
///  BoolElt : true if alg is central simple.
///            false if alg is not central simple or of unknown type
function known_csa(alg)
    if not ISA(Type(BaseRing(alg)), Fld) then
        // in this case, only M_n(D) where D is a division algebra is admissible
        // this yields false negatives
        if not Generic(alg) eq alg then
            return false;
        end if;

        // now we need to check whether BaseRing(alg) is a division algebra
        D := BaseRing(alg);
        if not ISA(Type(D), Alg) then
            return false;
        end if;
        if not ISA(Type(BaseRing(D)), Fld) then
            return false;
        end if;

        C := Center(D);
        for b in Basis(C) do
            if not IsScalar(b) then
                // the center of alg has an element which is not in BaseRing(alg) * 1
                // so alg is not central
                return false;
            end if;
        end for;

        // see if we can find out whether D is a division algebra
        try
            res := IsDivisionRing(D);
            // M_n(D) for D division algebra over a field is CSA.
            // this yields no false positives.
            return res;
        catch e
            // if we can't, return false. This yields false negatives
            return false;
        end try;
    end if;

    // in this case we are defined directly over a field.
    C := Center(alg);
    for b in Basis(C) do
        if not IsScalar(b) then
            // the center of alg has an element which is not in BaseRing(alg) * 1
            // so alg is not central
            return false;
        end if;
    end for;

    decomp := DirectSumDecomposition(alg);
    if not #decomp eq 1 then
        // not simple
        return false;
    end if;

    // This yields no false positives, because we have already established
    // that alg is defined over a field, where CSA can be checked completely
    return true;
end function;

/// Get a Basis for K over the prime field or another natural subfield without nontrivial involutions
///
/// INPUTS
///  FldNum or FldRat or FldCom or FldRe or FldFin K
/// OUTPUTS
///  SeqEnum[FldElt] Basis of K relative to PrimeField(K) (or another natural base field)
///  Fld the field over which the basis is taken
/// GUARANTEES
///  the returned field has no nontrivial field-involutions
function basis_to_prime_field(K)

    if ISA(Type(K), FldFin) then
        return Basis(K, PrimeField(K)), PrimeField(K);
    elif ISA(Type(K), FldNum) then
        return [K ! el : el in Basis(AbsoluteField(K))], Rationals();
    elif Type(K) eq FldCom then
        return [K ! [1, 0], K ! [0, 1]], RealField(K`Precision);
    elif Type(K) eq FldRat then
        return [K ! 1], K;
    elif Type(K) eq FldRe then
        return [K ! 1], K;
    else
        K; Type(K);
        error "basis_to_prime_field: field is not of a recognized type.";
    end if;
end function;
