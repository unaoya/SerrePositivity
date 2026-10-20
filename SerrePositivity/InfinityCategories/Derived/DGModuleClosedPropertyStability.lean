module
public import SerrePositivity.InfinityCategories.Derived.DGModuleClosedPropertyChoices
public import SerrePositivity.InfinityCategories.Stable.BicartesianCriterion
public import SerrePositivity.InfinityCategories.Stable.ExactFunctorChoice

/-!
概要：標準演算で閉じる全 dg 加群部分圏の安定性と包含の完全性。
方針：実双カルテジアンな選択と、周囲の同じ四角形への厳密な復元を使う。
規約：replete 性を要求しない。使われ方：β5 の射影的な加群の模型。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve DGNerve.HomotopyComparison SSet
open scoped Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable (P : RightModule A D → Prop) (hP : DGModuleClosedProperty A D P)
include hP

/-- 零加群を含む条件付き加群部分圏は実零対象を持つ。 -/
lemma dgClosedModule_hasZeroVertex : HasZeroVertex
    (dgNerve A (DGFullSubcategory (RightModule A D) P)) := by
  let Z : DGFullSubcategory (RightModule A D) P := ⟨zeroModule A D, hP.zero⟩
  refine ⟨Simplex.vertex Z, ?_, ?_⟩
  · apply isInitialVertex_of_fullInclusion A (RightModule A D) P
    rw [dgFunctorNerve_vertex]
    exact (dgModuleNerveZeroVertex_isZero A D).1
  · apply isTerminalVertex_of_fullInclusion A (RightModule A D) P
    rw [dgFunctorNerve_vertex]
    exact (dgModuleNerveZeroVertex_isZero A D).2
/-- 零・標準 cone・fiber で閉じる全 dg 加群部分圏の nerve は安定。 -/
theorem dgClosedModule_isStable : IsStable
    (dgNerve A (DGFullSubcategory (RightModule A D) P)) := by
  let := dgClosedModule_hasZeroVertex A D P hP
  exact isStable_of_bicartesian_choices (dgClosedModule_bicartesian_fiber_exists A D P hP)
    (dgClosedModule_bicartesian_cofiber_exists A D P hP)

/-- 各部分圏内の実辺には、周囲でも押し出しとなる cofiber 四角形がある。 -/
lemma dgClosedModule_cofiber_exists_preserved
    {x y : (dgNerve A (DGFullSubcategory (RightModule A D) P)) _⦋0⦌}
    (e : Truncated.Edge (X := (truncation 2).obj
      (dgNerve A (DGFullSubcategory (RightModule A D) P))) x y) :
    ∃ s : CofiberSquare e, IsPushoutSquare
      (s.square ≫ dgNerve.map (dgFullSubcategoryInclusion A (RightModule A D)
        (P))) := by
  obtain ⟨M, rfl⟩ := Simplex.vertexEquiv.symm.surjective x
  obtain ⟨N, rfl⟩ := Simplex.vertexEquiv.symm.surjective y
  let a := dgClosedModuleAmbientEdge A D P e
  let f := edgeClosed a
  let L := dgClosedModuleConeSquare A D P hP f M.property N.property
  have he : (dgModuleEdge A D f).edge = a.edge :=
    congrArg Truncated.Edge.edge (dgModuleEdge_edgeClosed A D a)
  let s : CofiberSquare e := {
    square := L
    zero_corner := dgFullSquareLift_zero_corner A _ _ _ _
      (dgModuleConeZeroTriangle A D f).zero_corner
    bottom_edge := by
      apply dgFullSquareLift_edge A (RightModule A D)
        (P) _ _ _ e
      rw [dgModuleConeSquare_bottom]
      exact congrArg SSet.yonedaEquiv.symm he
    isPushout := dgClosedModuleConeSquare_isPushout A D P hP f M.property N.property }
  refine ⟨s, ?_⟩
  change IsPushoutSquare (dgClosedModuleConeSquare A D P hP f M.property N.property ≫ _)
  dsimp only [dgClosedModuleConeSquare]
  rw [dgFullSquareLift_inclusion]
  exact dgModuleConeSquare_isPushout A D f

/-- 三角的条件で閉じた全 dg 加群の充満部分圏の包含は完全。 -/
theorem dgClosedModuleInclusion_isExactFunctor :
    IsExactFunctor (dgNerve.map (dgFullSubcategoryInclusion A (RightModule A D)
      (P))) :=
  isExactFunctor_of_preserves_chosen_cofibers _
    (dgFunctorNerve_preservesZeroVertices _) (dgClosedModule_cofiber_exists_preserved A D P hP)

end SerrePositivity.InfinityCategories
