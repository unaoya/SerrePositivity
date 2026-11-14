module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Triangles.DGStableObjectProperty
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.FunctorComparisons.DGFunctors.DGFunctorZeroObjects
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.BicartesianCriterion
/-!
概要：閉性を満たす全 dg 部分圏内に実双カルテジアン四角形を構成する。
方針：周囲の選択の四頂点を確認し、全単体を包含へ持ち上げる。
規約：指定実辺と周囲の実四角形を保持。使われ方：Verdier 列の零化部分。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D]
variable [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)] (P : D → Prop) (hP : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGStableObjectProperty A D P)
include hP
/-- 条件付き dg 部分圏は実零頂点を持つ。 -/
lemma dgStableSubcategory_hasZeroVertex : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.HasZeroVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A (DGFullSubcategory D P)) := by
  let z := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.chosenZeroVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)
  let Z : DGFullSubcategory D P := ⟨z.vertex.obj 0, hP.zero z.vertex z.isZero⟩
  refine ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex Z, ?_, ?_⟩
  · apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.isInitialVertex_of_fullInclusion A D P
    rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorNerve_vertex]
    exact (congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerve_vertex_obj A D z.vertex)).mpr z.isInitial
  · apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.isTerminalVertex_of_fullInclusion A D P
    rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorNerve_vertex]
    exact (congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerve_vertex_obj A D z.vertex)).mpr z.isTerminal
/-- 全実辺に、周囲での押し出し性を保持する双カルテジアンな cofiber がある。 -/
lemma dgStableSubcategory_cofiber_exists
    {x y : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A (DGFullSubcategory D P)) _⦋0⦌}
    (e : Truncated.Edge (X := (truncation 2).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A (DGFullSubcategory D P))) x y) :
    ∃ s : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.CofiberSquare e, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare s.square ∧ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare
      (s.square ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgFullSubcategoryInclusion A D P)) := by
  let q := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgFullSubcategoryInclusion A D P)
  let a := e.map ((truncation 2).map q)
  let r := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.chosenCofiberSquare (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D) a
  have h₀ : P ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex r.square 0 0).obj 0) := by
    rw [r.source_vertex]
    exact (x.obj 0).property
  have h₁ : P ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex r.square 1 0).obj 0) := by
    rw [r.target_vertex]
    exact (y.obj 0).property
  have hv : ∀ i j, P ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex r.square i j).obj 0) := by
    intro i j
    fin_cases i <;> fin_cases j
    · exact h₀
    · exact hP.zero _ r.zero_corner
    · exact h₁
    · exact hP.cofiber r.toZeroTriangle r.isPushout h₀ h₁
  let L := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFullSquareLift A D P r.square hv
  let s : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.CofiberSquare e := {
    square := L
    zero_corner := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFullSquareLift_zero_corner A D P _ hv r.zero_corner
    bottom_edge := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFullSquareLift_edge A D P _ hv _ e r.bottom_edge
    isPushout := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFullSquareLift_isPushout A D P _ hv r.isPushout }
  refine ⟨s, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFullSquareLift_isPullback A D P _ hv
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable.pullback_of_pushout r.toZeroTriangle r.isPushout), ?_⟩
  change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare (L ≫ q)
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFullSquareLift_inclusion]
  exact r.isPushout
/-- 全実辺に、周囲での引き戻し性を保持する双カルテジアンな fiber がある。 -/
lemma dgStableSubcategory_fiber_exists
    {x y : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A (DGFullSubcategory D P)) _⦋0⦌}
    (e : Truncated.Edge (X := (truncation 2).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A (DGFullSubcategory D P))) x y) :
    ∃ s : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.FiberSquare e, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare s.square := by
  let q := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgFullSubcategoryInclusion A D P)
  let a := e.map ((truncation 2).map q)
  let r := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.chosenFiberSquare (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D) a
  have hs : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex r.square 1 0 = q.app (Opposite.op ⦋0⦌) x :=
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareRightEdge_source r.square).symm.trans
      ((congrArg (fun t => (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D).δ 1 (SSet.yonedaEquiv t)) r.right_edge).trans
        ((congrArg ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D).δ 1) (SSet.yonedaEquiv.apply_symm_apply a.edge)).trans a.src_eq))
  have ht : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex r.square 1 1 = q.app (Opposite.op ⦋0⦌) y :=
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareRightEdge_target r.square).symm.trans
      ((congrArg (fun t => (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D).δ 0 (SSet.yonedaEquiv t)) r.right_edge).trans
        ((congrArg ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D).δ 0) (SSet.yonedaEquiv.apply_symm_apply a.edge)).trans a.tgt_eq))
  have h₁ : P ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex r.square 1 0).obj 0) := by
    rw [hs]
    exact (x.obj 0).property
  have h₂ : P ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex r.square 1 1).obj 0) := by
    rw [ht]
    exact (y.obj 0).property
  have hv : ∀ i j, P ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex r.square i j).obj 0) := by
    intro i j
    fin_cases i <;> fin_cases j
    · exact hP.fiber r.toZeroTriangle r.isPullback h₁ h₂
    · exact hP.zero _ r.zero_corner
    · exact h₁
    · exact h₂
  let s : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.FiberSquare e := {
    square := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFullSquareLift A D P r.square hv
    zero_corner := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFullSquareLift_zero_corner A D P _ hv r.zero_corner
    right_edge := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFullSquareLift_edge A D P _ hv _ e r.right_edge
    isPullback := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFullSquareLift_isPullback A D P _ hv r.isPullback }
  exact ⟨s, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFullSquareLift_isPushout A D P _ hv
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable.pushout_of_pullback r.toZeroTriangle r.isPullback)⟩
end SerrePositivity.InfinityCategories.Project.DerivedCategories
