module
public import SerrePositivity.KST.SConstruction.CutSupportImages

/-! # 支持条件による反対側の切断の消滅
概要：左支持の図式の右切断、右支持の図式の左切断は S_n C 内で零対象となる。
方針：切断後の全 Ar 成分が元の零となる支持領域に入ることを示す。
規約：零対象は点ごとの判定から実証明する。使われ方：支持部分圏の正規化の関手同型。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 左支持の図式の右切断は S_n C 自身の零対象。 -/
lemma cutLeftSupport_rightCut_isZero (n : ℕ) (k : Fin (n + 1)) (X : StableModel.{u})
    (v : (sConstruction n X.carrier) _⦋0⦌) (hv : (cutLeftSupport n k X).predicate v) :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex ((sMap X.carrier (cutCornerOrder k 1 1)).app (Opposite.op ⦋0⦌) v) := by
  apply gappedVertex_isZero_of_pointwise
  intro a
  obtain ⟨b, rfl⟩ := nerveEquiv.symm.surjective a
  have hb : k ≤ ((arMap (cutCornerOrder k 1 1)) b).down.val.1 := by
    change k ≤ cutEndpoint k b.down.val.1 1 1
    rw [cutEndpoint_one_one]
    exact le_max_right _ _
  have he := sMap_evaluate_vertex (cutCornerOrder k 1 1) v (ComposableArrows.mk₀ b)
  exact (congrArg _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex he).mpr (hv ⟨arMap (cutCornerOrder k 1 1) b, hb⟩)

/-- 右支持の図式の左切断は S_n C 自身の零対象。 -/
lemma cutRightSupport_leftCut_isZero (n : ℕ) (k : Fin (n + 1)) (X : StableModel.{u})
    (v : (sConstruction n X.carrier) _⦋0⦌) (hv : (cutRightSupport n k X).predicate v) :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex ((sMap X.carrier (cutCornerOrder k 0 0)).app (Opposite.op ⦋0⦌) v) := by
  apply gappedVertex_isZero_of_pointwise
  intro a
  obtain ⟨b, rfl⟩ := nerveEquiv.symm.surjective a
  have hb : ((arMap (cutCornerOrder k 0 0)) b).down.val.2 ≤ k := by
    change cutEndpoint k b.down.val.2 0 0 ≤ k
    rw [cutEndpoint_zero_zero]
    exact min_le_right _ _
  have he := sMap_evaluate_vertex (cutCornerOrder k 0 0) v (ComposableArrows.mk₀ b)
  exact (congrArg _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex he).mpr (hv ⟨arMap (cutCornerOrder k 0 0) b, hb⟩)

end SerrePositivity.KST.SConstruction
