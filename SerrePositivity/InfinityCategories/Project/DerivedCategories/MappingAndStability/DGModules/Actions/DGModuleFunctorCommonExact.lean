module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Actions.DGModuleSquareCommonMap
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.Nerves.DGNerveCommonMapZero
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Actions.DGModuleFunctorExact
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.MappingSpaces.UniverseZeroTriangle
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.QCatEquivalence
/-!
概要：独立の係数圏宇宙を持つ全 dg 加群間の関手の共通 nerve は完全である。
方針：同じ標準 cone の実四角形像の普遍性を持ち上げ、全 cofiber 比較で移送する。
規約：全加群圏の Small 仮定は不要。既存の混在宇宙 cone 比較を再利用する。
使われ方：任意の加群値 dg 関手の混在宇宙の完全性における kernel tensor。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v w t
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory MonoidalCategory DifferentialGraded SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (D : Type v) (C : Type w)
  [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D] [_root_.SerrePositivity.DifferentialGraded.DGCategory R C] [Small.{u} C]
  (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor R (_root_.SerrePositivity.DifferentialGraded.RightModule R D) (_root_.SerrePositivity.DifferentialGraded.RightModule R C))

lemma dgModuleFunctorCommon_cofiber_exists
    {x y : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleNerve R D) _⦋0⦌}
    (f : Truncated.Edge (X := (truncation 2).obj (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleNerve R D)) x y) :
    ∃ s : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.CofiberSquare f, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare
      (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftSquare.{max (u + 1) v, max (u + 1) v w t} s.square ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveCommonMap.{u, max (u + 1) v, max (u + 1) w, t} F) := by
  obtain ⟨M, rfl⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertexEquiv.symm.surjective x
  obtain ⟨N, rfl⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertexEquiv.symm.surjective y
  change ∃ s : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.CofiberSquare (X := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleNerve R D)
    (f : Truncated.Edge (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex M) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex N)), _
  rw [← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleEdge_edgeClosed R D f]
  refine ⟨_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleCofiberSquare R D (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.edgeClosed f), ?_⟩
  change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftSquare (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeSquare R D (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.edgeClosed f)) ≫ _)
  rw [← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeSquareData_square, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.map_square_common]
  apply (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.isPushoutSquare_iff_ulift _).1
  exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeSquare_isPushout R C (F.onClosed.map (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.edgeClosed f))).of_functorIso
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorConeDataFunctorIso R D C F (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.edgeClosed f))

lemma dgModuleFunctorCommonNerve_isExactFunctor :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveCommonMap.{u, max (u + 1) v, max (u + 1) w, t} F) where
  preservesZero := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveCommonMap_preservesZeroVertices F
  preservesCofiber t ht := by
    let f := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ t.down.square))
    let s : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.CofiberSquare f := {
      toZeroTriangle := t.down
      bottom_edge := (SSet.yonedaEquiv.symm_apply_apply _).symm
      isPushout := t.isCofiber_down ht }
    obtain ⟨r, hr⟩ := dgModuleFunctorCommon_cofiber_exists R D C F f
    obtain ⟨e⟩ := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.nonempty_cofiberSquareFunctorIso r s
    have he := (e.ulift.{max (u + 1) v, max (u + 1) v w t}).precomp
      (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftSquareIso.{max (u + 1) v, max (u + 1) v w t}).inv
    have hp := hr.of_functorIso (he.postcomp
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveCommonMap.{u, max (u + 1) v, max (u + 1) w, t} F))
    change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftSquare t.down.square ≫ _) at hp
    rwa [t.ulift_down_square] at hp

end SerrePositivity.InfinityCategories.Project.DerivedCategories
