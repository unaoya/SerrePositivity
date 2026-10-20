module
public import SerrePositivity.InfinityCategories.Derived.DGStableObjectProperty
public import SerrePositivity.InfinityCategories.Derived.DGFunctorZeroObjects
public import SerrePositivity.InfinityCategories.Stable.BicartesianCriterion
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
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]
variable [IsStable (dgNerve A D)] (P : D → Prop) (hP : DGStableObjectProperty A D P)
include hP
/-- 条件付き dg 部分圏は実零頂点を持つ。 -/
lemma dgStableSubcategory_hasZeroVertex : HasZeroVertex (dgNerve A (DGFullSubcategory D P)) := by
  let z := chosenZeroVertex (dgNerve A D)
  let Z : DGFullSubcategory D P := ⟨z.vertex.obj 0, hP.zero z.vertex z.isZero⟩
  refine ⟨Simplex.vertex Z, ?_, ?_⟩
  · apply isInitialVertex_of_fullInclusion A D P
    rw [dgFunctorNerve_vertex]
    exact (congrArg IsInitialVertex (dgNerve_vertex_obj A D z.vertex)).mpr z.isInitial
  · apply isTerminalVertex_of_fullInclusion A D P
    rw [dgFunctorNerve_vertex]
    exact (congrArg IsTerminalVertex (dgNerve_vertex_obj A D z.vertex)).mpr z.isTerminal
/-- 全実辺に、周囲での押し出し性を保持する双カルテジアンな cofiber がある。 -/
lemma dgStableSubcategory_cofiber_exists
    {x y : (dgNerve A (DGFullSubcategory D P)) _⦋0⦌}
    (e : Truncated.Edge (X := (truncation 2).obj (dgNerve A (DGFullSubcategory D P))) x y) :
    ∃ s : CofiberSquare e, IsPullbackSquare s.square ∧ IsPushoutSquare
      (s.square ≫ dgNerve.map (dgFullSubcategoryInclusion A D P)) := by
  let q := dgNerve.map (dgFullSubcategoryInclusion A D P)
  let a := e.map ((truncation 2).map q)
  let r := chosenCofiberSquare (X := dgNerve A D) a
  have h₀ : P ((squareVertex r.square 0 0).obj 0) := by
    rw [r.source_vertex]
    exact (x.obj 0).property
  have h₁ : P ((squareVertex r.square 1 0).obj 0) := by
    rw [r.target_vertex]
    exact (y.obj 0).property
  have hv : ∀ i j, P ((squareVertex r.square i j).obj 0) := by
    intro i j
    fin_cases i <;> fin_cases j
    · exact h₀
    · exact hP.zero _ r.zero_corner
    · exact h₁
    · exact hP.cofiber r.toZeroTriangle r.isPushout h₀ h₁
  let L := dgFullSquareLift A D P r.square hv
  let s : CofiberSquare e := {
    square := L
    zero_corner := dgFullSquareLift_zero_corner A D P _ hv r.zero_corner
    bottom_edge := dgFullSquareLift_edge A D P _ hv _ e r.bottom_edge
    isPushout := dgFullSquareLift_isPushout A D P _ hv r.isPushout }
  refine ⟨s, dgFullSquareLift_isPullback A D P _ hv
    (IsStable.pullback_of_pushout r.toZeroTriangle r.isPushout), ?_⟩
  change IsPushoutSquare (L ≫ q)
  rw [dgFullSquareLift_inclusion]
  exact r.isPushout
/-- 全実辺に、周囲での引き戻し性を保持する双カルテジアンな fiber がある。 -/
lemma dgStableSubcategory_fiber_exists
    {x y : (dgNerve A (DGFullSubcategory D P)) _⦋0⦌}
    (e : Truncated.Edge (X := (truncation 2).obj (dgNerve A (DGFullSubcategory D P))) x y) :
    ∃ s : FiberSquare e, IsPushoutSquare s.square := by
  let q := dgNerve.map (dgFullSubcategoryInclusion A D P)
  let a := e.map ((truncation 2).map q)
  let r := chosenFiberSquare (X := dgNerve A D) a
  have hs : squareVertex r.square 1 0 = q.app (Opposite.op ⦋0⦌) x :=
    (squareRightEdge_source r.square).symm.trans
      ((congrArg (fun t => (dgNerve A D).δ 1 (SSet.yonedaEquiv t)) r.right_edge).trans
        ((congrArg ((dgNerve A D).δ 1) (SSet.yonedaEquiv.apply_symm_apply a.edge)).trans a.src_eq))
  have ht : squareVertex r.square 1 1 = q.app (Opposite.op ⦋0⦌) y :=
    (squareRightEdge_target r.square).symm.trans
      ((congrArg (fun t => (dgNerve A D).δ 0 (SSet.yonedaEquiv t)) r.right_edge).trans
        ((congrArg ((dgNerve A D).δ 0) (SSet.yonedaEquiv.apply_symm_apply a.edge)).trans a.tgt_eq))
  have h₁ : P ((squareVertex r.square 1 0).obj 0) := by
    rw [hs]
    exact (x.obj 0).property
  have h₂ : P ((squareVertex r.square 1 1).obj 0) := by
    rw [ht]
    exact (y.obj 0).property
  have hv : ∀ i j, P ((squareVertex r.square i j).obj 0) := by
    intro i j
    fin_cases i <;> fin_cases j
    · exact hP.fiber r.toZeroTriangle r.isPullback h₁ h₂
    · exact hP.zero _ r.zero_corner
    · exact h₁
    · exact h₂
  let s : FiberSquare e := {
    square := dgFullSquareLift A D P r.square hv
    zero_corner := dgFullSquareLift_zero_corner A D P _ hv r.zero_corner
    right_edge := dgFullSquareLift_edge A D P _ hv _ e r.right_edge
    isPullback := dgFullSquareLift_isPullback A D P _ hv r.isPullback }
  exact ⟨s, dgFullSquareLift_isPushout A D P _ hv
    (IsStable.pushout_of_pullback r.toZeroTriangle r.isPullback)⟩
end SerrePositivity.InfinityCategories
