LoadPackage("transgrp");;
if LoadPackage("MeatAxe") = fail then
  Error("MeatAxe package unavailable");
fi;
SetPrintFormattingStatus("*stdout*", false);

F := GF(2);;
H := TransitiveGroup(12,90);;
S12 := SymmetricGroup(12);;
S24 := SymmetricGroup(24);;

OnSubgroupsByConjugation := function(U,g)
  return U^g;
end;

SupportOfVector := function(v)
  return Set(Filtered([1..12], i -> v[i] <> Zero(F)));
end;

RowsOfBasisMatrix := function(B)
  return List([1..Length(B)], i -> B[i]);
end;

CodeSupports := function(B)
  local V;
  V := VectorSpace(F, RowsOfBasisMatrix(B));
  return Set(List(Elements(V), SupportOfVector));
end;

WeightEnumerator := function(B)
  local V,out,v,w;
  V := VectorSpace(F, RowsOfBasisMatrix(B));
  out := List([0..12], i -> 0);
  for v in Elements(V) do
    w := Length(SupportOfVector(v));
    out[w+1] := out[w+1] + 1;
  od;
  return out;
end;

RadicalDimension := function(B)
  local Gm;
  Gm := B * TransposedMat(B);
  return Length(B) - RankMat(Gm);
end;

IsSelfDualBasis := function(B)
  return Length(B)=6 and RadicalDimension(B)=6;
end;

LiftTop := function(h)
  local img,i;
  img := [1..24];
  for i in [1..12] do
    img[2*i-1] := 2*(i^h)-1;
    img[2*i] := 2*(i^h);
  od;
  return PermList(img);
end;

FlipPerm := function(v)
  local img,i;
  img := [1..24];
  for i in [1..12] do
    if v[i] <> Zero(F) then
      img[2*i-1] := 2*i;
      img[2*i] := 2*i-1;
    fi;
  od;
  return PermList(img);
end;

SplitGroupFromBasis := function(B)
  local gens;
  gens := List(RowsOfBasisMatrix(B), FlipPerm);
  Append(gens, List(GeneratorsOfGroup(H), LiftTop));
  return Group(gens);
end;

OnCodes := function(C,g)
  return Set(List(C, S -> OnSets(S,g)));
end;

OrbitClassesOfCodes := function(N,codes)
  local remaining,classes,C,orb,cls,idxs;
  remaining := ShallowCopy(codes);
  classes := [];
  while Length(remaining)>0 do
    C := remaining[1];
    orb := Orbit(N,C,OnCodes);
    cls := Filtered(remaining,D -> D in orb);
    idxs := List(cls,D -> Position(codes,D));
    Add(classes,idxs);
    remaining := Filtered(remaining,D -> not D in orb);
  od;
  return classes;
end;

TwoBlocks := function(G)
  local j,B,BS;
  for j in [2..24] do
    B := [1,j];
    if IsBlock(G,[1..24],B) then
      BS := Set(Orbit(G,B,OnSets));
      if Length(BS)=12 and ForAll(BS,b -> Length(b)=2) then
        return BS;
      fi;
    fi;
  od;
  Error("no 12x2 block system");
end;

FlipVectorInKernel := function(blocks,g)
  return Vector(F,List(blocks,b -> if b[1]^g=b[1] then 0 else 1 fi));
end;

KernelCodeData := function(n)
  local G,blocks,ah,Q,K,rows,B,C,c,Cstd;
  G := TransitiveGroup(24,n);
  blocks := TwoBlocks(G);
  ah := ActionHomomorphism(G,blocks,OnSets);
  Q := Image(ah);
  K := Kernel(ah);
  rows := List(GeneratorsOfGroup(K), k -> FlipVectorInKernel(blocks,k));
  B := Matrix(F,BasisVectors(Basis(VectorSpace(F,rows))));
  C := CodeSupports(B);
  c := RepresentativeAction(S12,Q,H,OnSubgroupsByConjugation);
  if c=fail then
    Error("could not align quotient with 12T90");
  fi;
  Cstd := OnCodes(C,c);
  return rec(n:=n,group:=G,blocks:=blocks,quotient:=Q,kernel:=K,basis:=B,
             code:=C,aligner:=c,codestd:=Cstd,
             rad:=RadicalDimension(B),we:=WeightEnumerator(B));
end;

TargetWE := [1,0,0,0,15,0,32,0,15,0,0,0,1];;
M := PermutationGModule(H,F);;
allBases := MTX.BasesSubmodules(M);;
Print("H_ORDER|",Size(H),"\n");
Print("ALL_SUBMODULES|",Length(allBases),"\n");

records := [];;
for idx in [1..Length(allBases)] do
  B := allBases[idx];
  if Length(B)=6 and WeightEnumerator(B)=TargetWE then
    rad := RadicalDimension(B);
    C := CodeSupports(B);
    G := SplitGroupFromBasis(B);
    tid := TransitiveIdentification(G);
    Add(records,rec(idx:=idx,basis:=B,code:=C,rad:=rad,
                    selfdual:=IsSelfDualBasis(B),tid:=tid,gorder:=Size(G)));
    Print("MATCH|",Length(records),"|SUBIDX|",idx,"|RAD|",rad,
          "|SELF|",IsSelfDualBasis(B),"|TID|",tid,"|ORDER|",Size(G),
          "|BASIS|",RowsOfBasisMatrix(B),"\n");
  fi;
od;

Print("MATCH_COUNT|",Length(records),"\n");
for rdim in [0..6] do
  Print("RAD_COUNT|",rdim,"|",Length(Filtered(records,r -> r.rad=rdim)),"\n");
od;
Print("TID_SET|",Set(List(records,r -> r.tid)),"\n");

N12 := Normalizer(S12,H);;
Print("N12_ORDER|",Size(N12),"\n");
selfRecords := Filtered(records,r -> r.rad=6);;
rad4Records := Filtered(records,r -> r.rad=4);;
selfCodes := List(selfRecords,r -> r.code);;
rad4Codes := List(rad4Records,r -> r.code);;
Print("SELF_COUNT|",Length(selfCodes),"\n");
Print("RAD4_COUNT|",Length(rad4Codes),"\n");
if Length(selfCodes)>0 then
  Print("SELF_NORMALIZER_ORBITS|",OrbitClassesOfCodes(N12,selfCodes),"\n");
fi;
if Length(rad4Codes)>0 then
  Print("RAD4_NORMALIZER_ORBITS|",OrbitClassesOfCodes(N12,rad4Codes),"\n");
fi;

D1 := KernelCodeData(11153);;
D2 := KernelCodeData(11731);;
for D in [D1,D2] do
  Print("LIB|24T",D.n,"|ORDER|",Size(D.group),
        "|QID|",TransitiveIdentification(D.quotient),
        "|QORDER|",Size(D.quotient),"|KORDER|",Size(D.kernel),
        "|DIM|",Length(D.basis),"|RAD|",D.rad,"|SELF|",(D.rad=6),
        "|WE|",D.we,"|ALIGNER|",D.aligner,
        "|BASIS|",RowsOfBasisMatrix(D.basis),"\n");
  exactpos := PositionProperty(records,r -> r.code=D.codestd);
  Print("LIB_EXACT_ENUM_POS|24T",D.n,"|",exactpos,"\n");
  if exactpos=fail then
    hits := [];
    for j in [1..Length(records)] do
      cc := RepresentativeAction(N12,records[j].code,D.codestd,OnCodes);
      if cc<>fail then Add(hits,j); fi;
    od;
    Print("LIB_NORMALIZER_HITS|24T",D.n,"|",hits,"\n");
  else
    Print("LIB_ENUM_RECORD|24T",D.n,"|RAD|",records[exactpos].rad,
          "|TID|",records[exactpos].tid,"\n");
  fi;
od;

OnSubs := function(U,g) return U^g; end;
Print("LIB_S24_CONJUGATOR|",RepresentativeAction(S24,D1.group,D2.group,OnSubs),"\n");
QUIT;
