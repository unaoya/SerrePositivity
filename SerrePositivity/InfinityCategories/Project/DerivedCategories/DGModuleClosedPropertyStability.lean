module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleClosedPropertyChoices
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.BicartesianCriterion
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExactFunctorChoice

/-!
概要：標準演算で閉じる全 dg 加群部分圏の安定性と包含の完全性。
方針：実双カルテジアンな選択と、周囲の同じ四角形への厳密な復元を使う。
規約：replete 性を要求しない。使われ方：β5 の射影的な加群の模型。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D]
variable (P : RightModule A D → Prop) (hP : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleClosedProperty A D P)
include hP

/-- 零加群を含む条件付き加群部分圏は実零対象を持つ。 -/
lemma dgClosedModule_hasZeroVertex : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.HasZeroVertex
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A (DGFullSubcategory (RightModule A D) P)) := by
  let Z : _root_.SerrePositivity.DifferentialGraded.DGFullSubcategory (_root_.SerrePositivity.DifferentialGraded.RightModule A D) P := ⟨_root_.SerrePositivity.DifferentialGraded.zeroModule A D, hP.zero⟩
  refine ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex Z, ?_, ?_⟩
  · apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.isInitialVertex_of_fullInclusion A (RightModule A D) P
    rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorNerve_vertex]
    exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleNerveZeroVertex_isZero A D).1
  · apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.isTerminalVertex_of_fullInclusion A (RightModule A D) P
    rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorNerve_vertex]
    exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleNerveZeroVertex_isZero A D).2
/-- 零・標準 cone・fiber で閉じる全 dg 加群部分圏の nerve は安定。 -/
theorem dgClosedModule_isStable : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A (DGFullSubcategory (RightModule A D) P)) := by
  let := dgClosedModule_hasZeroVertex A D P hP
  exact _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.isStable_of_bicartesian_choices (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedModule_bicartesian_fiber_exists A D P hP)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedModule_bicartesian_cofiber_exists A D P hP)

/-- 各部分圏内の実辺には、周囲でも押し出しとなる cofiber 四角形がある。 -/
lemma dgClosedModule_cofiber_exists_preserved
    {x y : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A (DGFullSubcategory (RightModule A D) P)) _⦋0⦌}
    (e : Truncated.Edge (X := (truncation 2).obj
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A (DGFullSubcategory (RightModule A D) P))) x y) :
    ∃ s : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.CofiberSquare e, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare
      (s.square ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgFullSubcategoryInclusion A (RightModule A D)
        (P))) := by
  obtain ⟨M, rfl⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertexEquiv.symm.surjective x
  obtain ⟨N, rfl⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertexEquiv.symm.surjective y
  let a := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedModuleAmbientEdge A D P e
  let f := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.edgeClosed a
  let L := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedModuleConeSquare A D P hP f M.property N.property
  have he : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleEdge A D f).edge = a.edge :=
    congrArg Truncated.Edge.edge (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleEdge_edgeClosed A D a)
  let s : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.CofiberSquare e := {
    square := L
    zero_corner := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFullSquareLift_zero_corner A _ _ _ _
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeZeroTriangle A D f).zero_corner
    bottom_edge := by
      apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFullSquareLift_edge A (RightModule A D)
        (P) _ _ _ e
      rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeSquare_bottom]
      exact congrArg SSet.yonedaEquiv.symm he
    isPushout := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedModuleConeSquare_isPushout A D P hP f M.property N.property }
  refine ⟨s, ?_⟩
  change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedModuleConeSquare A D P hP f M.property N.property ≫ _)
  dsimp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedModuleConeSquare]
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFullSquareLift_inclusion]
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeSquare_isPushout A D f

/-- 三角的条件で閉じた全 dg 加群の充満部分圏の包含は完全。 -/
theorem dgClosedModuleInclusion_isExactFunctor :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgFullSubcategoryInclusion A (RightModule A D)
      (P))) :=
  _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.isExactFunctor_of_preserves_chosen_cofibers _
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorNerve_preservesZeroVertices _) (dgClosedModule_cofiber_exists_preserved A D P hP)

end SerrePositivity.InfinityCategories.Project.DerivedCategories
