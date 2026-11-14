module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.FunctorComparisons.EnrichedFunctors.SuspensionVertexNaturality
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Triangles.StableHomotopyChainMap

/-! # D3 による suspension と一回シフトの比較の自然性

概要：対象ごとの suspension 比較は h D(S) の鎖写像の類に対して自然。
方針：標準 suspension 頂点への自然性、Qh と Q、cone 同型、Q のシフト比較を合成する。
規約：安定構造からの suspension を用いる。使われ方：D7 の CommShift の構成。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (S : Type u) [CommRing S] [HasDerivedCategory.{w} (ModuleCat.{u} S)]

/-- 対象比較を標準 suspension 頂点への比較を使って展開する。 -/
lemma derivedSuspensionObjectIso_hom (X : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree S) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSuspensionObjectIso S X).hom =
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedStableHomotopyEquivalence S).functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeSuspensionVertexIso X).hom ≫
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedStableHomotopyEquivalenceVertexIso S (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeSuspensionObject X)).hom ≫
        DerivedCategory.Q.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeSuspensionComplexIso X).hom ≫
        ((DerivedCategory.Q.commShiftIso (1 : ℤ)).app X.val).hom := by
  simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSuspensionObjectIso, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeSuspensionVertexIso, Iso.trans_hom,
    Functor.mapIso_hom, eqToIso.hom, Functor.map_comp, eqToHom_map, Category.assoc]

/-- D3 による suspension の対象比較は鎖写像の h の類に対して自然。 -/
lemma derivedSuspensionObjectIso_naturality {X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree S} (a : X.val ⟶ Y.val) :
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedStableHomotopyEquivalence S).functor.map
        ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.suspensionFunctor (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory S)).map
          (SSet.Truncated.HomotopyCategory.homMk
            (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedChainMapEdge (x := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex X) (y := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex Y) a))) ≫
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSuspensionObjectIso S Y).hom =
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSuspensionObjectIso S X).hom ≫ (DerivedCategory.Q.map a)⟦(1 : ℤ)⟧' := by
  let F := (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedStableHomotopyEquivalence S).functor
  let f := SSet.Truncated.HomotopyCategory.homMk
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedChainMapEdge (x := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex X) (y := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex Y) a)
  let g := SSet.Truncated.HomotopyCategory.homMk
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedChainMapEdge (x := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeSuspensionObject X))
      (y := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeSuspensionObject Y)) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeSuspensionComplexMap a))
  have hSusp : F.map ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.suspensionFunctor (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory S)).map f) ≫
      F.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeSuspensionVertexIso Y).hom =
      F.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeSuspensionVertexIso X).hom ≫ F.map g := by
    simpa only [Functor.map_comp] using congrArg F.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeSuspensionVertexIso_naturality a)
  have hV := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedStableHomotopyEquivalenceVertexIso_naturality S
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeSuspensionComplexMap a)
  have hQ := congrArg DerivedCategory.Q.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeSuspensionComplexIso_naturality a)
  simp only [Functor.map_comp] at hQ
  have hC := ((DerivedCategory.Q.commShiftIso (1 : ℤ)).hom.naturality a)
  rw [derivedSuspensionObjectIso_hom, derivedSuspensionObjectIso_hom]
  change F.map ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.suspensionFunctor (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory S)).map f) ≫ _ = _
  calc
    _ = (F.map ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.suspensionFunctor (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory S)).map f) ≫
        F.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeSuspensionVertexIso Y).hom) ≫
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedStableHomotopyEquivalenceVertexIso S (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeSuspensionObject Y)).hom ≫
        DerivedCategory.Q.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeSuspensionComplexIso Y).hom ≫
        ((DerivedCategory.Q.commShiftIso (1 : ℤ)).app Y.val).hom := by simp only [Category.assoc, F]
    _ = (F.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeSuspensionVertexIso X).hom ≫ F.map g) ≫
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedStableHomotopyEquivalenceVertexIso S (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeSuspensionObject Y)).hom ≫
        DerivedCategory.Q.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeSuspensionComplexIso Y).hom ≫
        ((DerivedCategory.Q.commShiftIso (1 : ℤ)).app Y.val).hom := by rw [hSusp]
    _ = F.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeSuspensionVertexIso X).hom ≫
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedStableHomotopyEquivalenceVertexIso S (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeSuspensionObject X)).hom ≫
        (DerivedCategory.Q.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeSuspensionComplexMap a) ≫
          DerivedCategory.Q.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeSuspensionComplexIso Y).hom) ≫
        ((DerivedCategory.Q.commShiftIso (1 : ℤ)).app Y.val).hom := by
      simpa only [Category.assoc, F, Functor.comp_map, Iso.app_hom] using congrArg
        (fun z => F.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeSuspensionVertexIso X).hom ≫ z ≫
          DerivedCategory.Q.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeSuspensionComplexIso Y).hom ≫
          ((DerivedCategory.Q.commShiftIso (1 : ℤ)).app Y.val).hom) hV
    _ = F.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeSuspensionVertexIso X).hom ≫
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedStableHomotopyEquivalenceVertexIso S (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeSuspensionObject X)).hom ≫
        (DerivedCategory.Q.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeSuspensionComplexIso X).hom ≫
          DerivedCategory.Q.map (a⟦(1 : ℤ)⟧')) ≫
        ((DerivedCategory.Q.commShiftIso (1 : ℤ)).app Y.val).hom := by rw [hQ]
    _ = _ := by
      simpa only [Category.assoc, F, Functor.comp_map, Iso.app_hom] using congrArg
        (fun z => F.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeSuspensionVertexIso X).hom ≫
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedStableHomotopyEquivalenceVertexIso S (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeSuspensionObject X)).hom ≫
          DerivedCategory.Q.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeSuspensionComplexIso X).hom ≫ z) hC

end SerrePositivity.InfinityCategories.Project.DerivedCategories
