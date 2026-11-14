module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.FunctorComparisons.EnrichedFunctors.SuspensionObjectNaturality
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.HomSpaces.HomotopyChainMapSurjectivity

/-! # D3 比較の suspension と導来圏シフトの自然な対象比較

概要：D3 比較の前後の一回シフトを、すべての定値頂点間の h の射に対して自然に比較する。
方針：Q の対象を D3 の対象へ戻し、すべての h の射を鎖写像で代表する。
規約：全整数の CommShift は後続。使われ方：D7 の自然同型の組み立て。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (S : Type u) [CommRing S] [HasDerivedCategory.{w} (ModuleCat.{u} S)]

/-- suspension の D3 像と D3 の像の一回シフトの比較。 -/
def derivedSuspensionShiftObjectIso (X : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree S) :
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedStableHomotopyEquivalence S).functor.obj
      ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.suspensionFunctor (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory S)).obj
        (SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex X))) ≅
      ((_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedStableHomotopyEquivalence S).functor.obj
        (SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex X)))⟦(1 : ℤ)⟧ :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSuspensionObjectIso S X ≪≫
    (shiftFunctor _ (1 : ℤ)).mapIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedStableHomotopyEquivalenceVertexIso S X).symm

/-- 一回シフト比較は鎖写像の類に対して自然。 -/
lemma derivedSuspensionShiftObjectIso_naturality_chainMap {X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree S}
    (a : X.val ⟶ Y.val) :
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedStableHomotopyEquivalence S).functor.map
        ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.suspensionFunctor (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory S)).map
          (SSet.Truncated.HomotopyCategory.homMk
            (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedChainMapEdge (x := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex X) (y := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex Y) a))) ≫
      (derivedSuspensionShiftObjectIso S Y).hom =
    (derivedSuspensionShiftObjectIso S X).hom ≫
      ((_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedStableHomotopyEquivalence S).functor.map
        (SSet.Truncated.HomotopyCategory.homMk
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedChainMapEdge (x := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex X) (y := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex Y) a)))⟦(1 : ℤ)⟧' := by
  let F := (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedStableHomotopyEquivalence S).functor
  let f := SSet.Truncated.HomotopyCategory.homMk
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedChainMapEdge (x := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex X) (y := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex Y) a)
  let VX := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedStableHomotopyEquivalenceVertexIso S X
  let VY := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedStableHomotopyEquivalenceVertexIso S Y
  have hV := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedStableHomotopyEquivalenceVertexIso_naturality S a
  change F.map f ≫ VY.hom = VX.hom ≫ DerivedCategory.Q.map a at hV
  have hInv : DerivedCategory.Q.map a ≫ VY.inv = VX.inv ≫ F.map f := by
    calc
      _ = VX.inv ≫ (VX.hom ≫ DerivedCategory.Q.map a) ≫ VY.inv := by simp
      _ = VX.inv ≫ (F.map f ≫ VY.hom) ≫ VY.inv := by rw [← hV]
      _ = _ := by simp
  have hShift := congrArg (shiftFunctor (DerivedCategory (ModuleCat S)) (1 : ℤ)).map hInv
  simp only [Functor.map_comp] at hShift
  have h := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSuspensionObjectIso_naturality S a
  dsimp only [derivedSuspensionShiftObjectIso, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom]
  calc
    _ = (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSuspensionObjectIso S X).hom ≫
        ((DerivedCategory.Q.map a)⟦(1 : ℤ)⟧' ≫ VY.inv⟦(1 : ℤ)⟧') := by
      simpa only [Category.assoc, F, f, VY] using congrArg
        (fun z => z ≫ VY.inv⟦(1 : ℤ)⟧') h
    _ = (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSuspensionObjectIso S X).hom ≫
        (VX.inv⟦(1 : ℤ)⟧' ≫ (F.map f)⟦(1 : ℤ)⟧') := by rw [hShift]
    _ = _ := by simp only [Category.assoc, F, f, VX]

/-- 一回シフト比較は、定値頂点間のすべての h D(S) の射に対して自然。 -/
lemma derivedSuspensionShiftObjectIso_naturality {X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree S}
    (f : (SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex X) :
      _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedStableHomotopyCategory S) ⟶ SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex Y)) :
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedStableHomotopyEquivalence S).functor.map
        ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.suspensionFunctor (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory S)).map f) ≫
      (derivedSuspensionShiftObjectIso S Y).hom =
    (derivedSuspensionShiftObjectIso S X).hom ≫
      ((_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedStableHomotopyEquivalence S).functor.map f)⟦(1 : ℤ)⟧' := by
  obtain ⟨a, rfl⟩ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedHomotopyHom_chainMap_surjective f
  exact derivedSuspensionShiftObjectIso_naturality_chainMap S a

end SerrePositivity.InfinityCategories.Project.DerivedCategories
