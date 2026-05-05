#############################################################################
# 4-dimensional deleted permutation quotient of A6 over GF(p), p = 2 or 3
#############################################################################

DeletedPermQuotientMatrix := function(g, p)
    local F, M, i, a, b, coeffs, j, col;

    F := GF(p);
    M := NullMat(4, 4, F);

    # v_i = e_i - e_6 for i=1,...,5, then quotient by v_1+...+v_5 = 0
    # basis of quotient: images of v_1,...,v_4

    for i in [1..4] do
        a := i ^ g;
        b := 6 ^ g;

        coeffs := [0,0,0,0,0];

        if a <> 6 then
            coeffs[a] := coeffs[a] + 1;
        fi;
        if b <> 6 then
            coeffs[b] := coeffs[b] - 1;
        fi;

        # eliminate v_5 using v_5 = -(v_1+v_2+v_3+v_4)
        col := [];
        for j in [1..4] do
            Add(col, coeffs[j] - coeffs[5]);
        od;

        for j in [1..4] do
            M[j][i] := col[j] * One(F);
        od;
    od;

    return M;
end;

#############################################################################
# Build (Z/pZ)^4 : A6 as affine matrices, then convert to permutation group
#############################################################################

AffineSemidirectA6 := function(p)
    local F, A6, gensA6, mats, gens, d, i, T, L, g, Gmat, iso, j;

    F := GF(p);
    d := 4;
    A6 := AlternatingGroup(6);
    gensA6 := GeneratorsOfGroup(A6);
    mats := List(gensA6, g -> DeletedPermQuotientMatrix(g, p));

    gens := [];

    # translations
    for i in [1..d] do
        T := IdentityMat(d+1, F);
        T[i][d+1] := One(F);
        Add(gens, T);
    od;

    # linear part
    for g in mats do
        L := IdentityMat(d+1, F);
        for i in [1..d] do
            for j in [1..d] do
                L[i][j] := g[i][j];
            od;
        od;
        Add(gens, L);
    od;

    Gmat := Group(gens);
    iso := IsomorphismPermGroup(Gmat);
    return Image(iso);
end;

#############################################################################
# Character of exterior cube:
# chi_{Λ^3 V}(g) = (chi(g)^3 - 3 chi(g) chi(g^2) + 2 chi(g^3))/6
#############################################################################

ExteriorCubeCharacter := function(tbl, chi)
    local pm2, pm3, vals, k, a, b, c;

    pm2 := PowerMap(tbl, 2);
    pm3 := PowerMap(tbl, 3);
    vals := [];

    for k in [1..NrConjugacyClasses(tbl)] do
        a := chi[k];
        b := chi[pm2[k]];
        c := chi[pm3[k]];
        Add(vals, (a^3 - 3*a*b + 2*c) / 6);
    od;

    return Character(tbl, vals);
end;

#############################################################################
# All degree-10 complex characters = nonnegative integer sums of irreducibles
#############################################################################

Degree10Characters := function(tbl)
    local irr, degs, out, zerochi, recfun;

    irr := Irr(tbl);
    degs := List(irr, chi -> chi[1]);
    out := [];
    zerochi := 0 * irr[1];

    recfun := function(pos, remaining, current)
        local m;

        if remaining = 0 then
            Add(out, current);
            return;
        fi;

        if pos > Length(irr) then
            return;
        fi;

        # skip irr[pos]
        recfun(pos + 1, remaining, current);

        # use m copies of irr[pos]
        for m in [1 .. Int(remaining / degs[pos])] do
            recfun(pos + 1, remaining - m * degs[pos], current + m * irr[pos]);
        od;
    end;

    recfun(1, 10, zerochi);
    return out;
end;

#############################################################################
# Check whether H has a degree-10 complex representation V with
# multiplicity of the trivial rep in Λ^3 V equal to 1
#############################################################################

QualifyingFaithfulDegree10Characters := function(H)
    local tbl, deg10, good, chi, ext3, mult, triv, ker;

    tbl := CharacterTable(H);
    deg10 := Degree10Characters(tbl);
    triv := TrivialCharacter(tbl);
    good := [];

    for chi in deg10 do
        ker := KernelOfCharacter(chi);
        if Size(ker) <> 1 then
            continue;
        fi;

        ext3 := ExteriorCubeCharacter(tbl, chi);
        mult := ScalarProduct(tbl, ext3, triv);

        if mult = 1 then
            Add(good, chi);
        fi;
    od;

    return good;
end;
#############################################################################
# Search subgroup conjugacy classes with order >= 2520
#############################################################################

SearchGroupFaithful := function(G, label)
    local classes, bigclasses, C, H, good, count;

    Print("\n====================================================\n");
    Print("Searching subgroups of ", label, "\n");
    Print("Order = ", Size(G), "\n");
    Print("====================================================\n");

    classes := ConjugacyClassesSubgroups(G);
    bigclasses := Filtered(classes, C -> Size(Representative(C)) >= 2520);

    Print("Conjugacy classes of subgroups: ", Length(classes), "\n");
    Print("Classes with representative of order >= 2520: ", Length(bigclasses), "\n");

    count := 0;
    for C in bigclasses do
        H := Representative(C);
        good := QualifyingFaithfulDegree10Characters(H);

        if Length(good) > 0 then
            count := count + 1;
            Print("\nMatch #", count, "\n");
            Print("Order: ", Size(H), "\n");
            Print("Structure: ", StructureDescription(H), "\n");
            Print("Number of faithful degree-10 characters with <Lambda^3(V),1> = 1: ",
                  Length(good), "\n");
        fi;
    od;

    if count = 0 then
        Print("\nNo matching subgroup of order >= 2520 found.\n");
    fi;
end;

#############################################################################
# Ambient groups
#############################################################################

G5 := PSL(3,4);
if not IsPermGroup(G5) then
    G5 := Image(IsomorphismPermGroup(G5));
fi;

G7 := AffineSemidirectA6(2);   # (Z/2Z)^4 : A6
Gx := AffineSemidirectA6(3);   # (Z/3Z)^4 : A6

#############################################################################
# Run
#############################################################################

SearchGroupFaithful(G5, "PSL(3,4)");
SearchGroupFaithful(G7, "(Z/2Z)^4 : A6");
SearchGroupFaithful(Gx, "(Z/3Z)^4 : A6");