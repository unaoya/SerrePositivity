module
public import SerrePositivity.InfinityCategories.Derived.SuspensionVertexNaturality
public import SerrePositivity.InfinityCategories.Derived.StableHomotopyChainMap

/-! # D3 による suspension と一回シフトの比較の自然性

概要：対象ごとの suspension 比較は h D(S) の鎖写像の類に対して自然。
方針：標準 suspension 頂点への自然性、Qh と Q、cone 同型、Q のシフト比較を合成する。
規約：安定構造からの suspension を用いる。使われ方：D7 の CommShift の構成。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u w
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
variable (S : Type u) [CommRing S] [HasDerivedCategory.{w} (ModuleCat.{u} S)]

/-- 対象比較を標準 suspension 頂点への比較を使って展開する。 -/
lemma derivedSuspensionObjectIso_hom (X : Semifree S) :
    (derivedSuspensionObjectIso S X).hom =
      (derivedStableHomotopyEquivalence S).functor.map (semifreeSuspensionVertexIso X).hom ≫
        (derivedStableHomotopyEquivalenceVertexIso S (semifreeSuspensionObject X)).hom ≫
        DerivedCategory.Q.map (semifreeSuspensionComplexIso X).hom ≫
        ((DerivedCategory.Q.commShiftIso (1 : ℤ)).app X.val).hom := by
  simp only [derivedSuspensionObjectIso, semifreeSuspensionVertexIso, Iso.trans_hom,
    Functor.mapIso_hom, eqToIso.hom, Functor.map_comp, eqToHom_map, Category.assoc]

/-- D3 による suspension の対象比較は鎖写像の h の類に対して自然。 -/
lemma derivedSuspensionObjectIso_naturality {X Y : Semifree S} (a : X.val ⟶ Y.val) :
    (derivedStableHomotopyEquivalence S).functor.map
        ((suspensionFunctor (derivedInfinityCategory S)).map
          (SSet.Truncated.HomotopyCategory.homMk
            (derivedChainMapEdge (x := Simplex.vertex X) (y := Simplex.vertex Y) a))) ≫
      (derivedSuspensionObjectIso S Y).hom =
    (derivedSuspensionObjectIso S X).hom ≫ (DerivedCategory.Q.map a)⟦(1 : ℤ)⟧' := by
  let F := (derivedStableHomotopyEquivalence S).functor
  let f := SSet.Truncated.HomotopyCategory.homMk
    (derivedChainMapEdge (x := Simplex.vertex X) (y := Simplex.vertex Y) a)
  let g := SSet.Truncated.HomotopyCategory.homMk
    (derivedChainMapEdge (x := Simplex.vertex (semifreeSuspensionObject X))
      (y := Simplex.vertex (semifreeSuspensionObject Y)) (semifreeSuspensionComplexMap a))
  have hSusp : F.map ((suspensionFunctor (derivedInfinityCategory S)).map f) ≫
      F.map (semifreeSuspensionVertexIso Y).hom =
      F.map (semifreeSuspensionVertexIso X).hom ≫ F.map g := by
    simpa only [Functor.map_comp] using congrArg F.map (semifreeSuspensionVertexIso_naturality a)
  have hV := derivedStableHomotopyEquivalenceVertexIso_naturality S
    (semifreeSuspensionComplexMap a)
  have hQ := congrArg DerivedCategory.Q.map (semifreeSuspensionComplexIso_naturality a)
  simp only [Functor.map_comp] at hQ
  have hC := ((DerivedCategory.Q.commShiftIso (1 : ℤ)).hom.naturality a)
  rw [derivedSuspensionObjectIso_hom, derivedSuspensionObjectIso_hom]
  change F.map ((suspensionFunctor (derivedInfinityCategory S)).map f) ≫ _ = _
  calc
    _ = (F.map ((suspensionFunctor (derivedInfinityCategory S)).map f) ≫
        F.map (semifreeSuspensionVertexIso Y).hom) ≫
        (derivedStableHomotopyEquivalenceVertexIso S (semifreeSuspensionObject Y)).hom ≫
        DerivedCategory.Q.map (semifreeSuspensionComplexIso Y).hom ≫
        ((DerivedCategory.Q.commShiftIso (1 : ℤ)).app Y.val).hom := by simp only [Category.assoc, F]
    _ = (F.map (semifreeSuspensionVertexIso X).hom ≫ F.map g) ≫
        (derivedStableHomotopyEquivalenceVertexIso S (semifreeSuspensionObject Y)).hom ≫
        DerivedCategory.Q.map (semifreeSuspensionComplexIso Y).hom ≫
        ((DerivedCategory.Q.commShiftIso (1 : ℤ)).app Y.val).hom := by rw [hSusp]
    _ = F.map (semifreeSuspensionVertexIso X).hom ≫
        (derivedStableHomotopyEquivalenceVertexIso S (semifreeSuspensionObject X)).hom ≫
        (DerivedCategory.Q.map (semifreeSuspensionComplexMap a) ≫
          DerivedCategory.Q.map (semifreeSuspensionComplexIso Y).hom) ≫
        ((DerivedCategory.Q.commShiftIso (1 : ℤ)).app Y.val).hom := by
      simpa only [Category.assoc, F, Functor.comp_map, Iso.app_hom] using congrArg
        (fun z => F.map (semifreeSuspensionVertexIso X).hom ≫ z ≫
          DerivedCategory.Q.map (semifreeSuspensionComplexIso Y).hom ≫
          ((DerivedCategory.Q.commShiftIso (1 : ℤ)).app Y.val).hom) hV
    _ = F.map (semifreeSuspensionVertexIso X).hom ≫
        (derivedStableHomotopyEquivalenceVertexIso S (semifreeSuspensionObject X)).hom ≫
        (DerivedCategory.Q.map (semifreeSuspensionComplexIso X).hom ≫
          DerivedCategory.Q.map (a⟦(1 : ℤ)⟧')) ≫
        ((DerivedCategory.Q.commShiftIso (1 : ℤ)).app Y.val).hom := by rw [hQ]
    _ = _ := by
      simpa only [Category.assoc, F, Functor.comp_map, Iso.app_hom] using congrArg
        (fun z => F.map (semifreeSuspensionVertexIso X).hom ≫
          (derivedStableHomotopyEquivalenceVertexIso S (semifreeSuspensionObject X)).hom ≫
          DerivedCategory.Q.map (semifreeSuspensionComplexIso X).hom ≫ z) hC

end SerrePositivity.InfinityCategories
