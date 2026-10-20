module
public import SerrePositivity.InfinityCategories.Derived.DGLastHornGeneralRefinedData
public import SerrePositivity.InfinityCategories.Derived.DGLastHornGeneralFinalEdge
public import SerrePositivity.InfinityCategories.Derived.DGInitialRefinementComponents
public import SerrePositivity.InfinityCategories.DGNerve.DataRhsComponents

/-! # 一般細分ホーンの二残差・対象・最後辺の厳密輸送

概要：全回収データの一致から、R・K の閉前合成と最後辺の保存を読む。
方針：同じ集合・端点・次数の rhs と成分の異種等号を接続する。
規約：対象族の等式を保持する。使われ方：追加分母後の二未知解の実細分への接続。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
open scoped Simplicial
variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D] {n : ℕ}
variable (σ : (Λ[n + 2, Fin.last (n + 2)] : SSet.{max u v}) ⟶ dgNerve A D) (q : D)
variable (s : ForgetEnrichment.of (Complex A) q ⟶
  ForgetEnrichment.of (Complex A) ((HornData.knownData σ).obj 0))

/-- 新ホーンの始対象は、同じ指定細分対象 q。 -/
lemma dgGeneralLastHornSourceRefinement_obj_zero :
    (HornData.knownData (dgGeneralLastHornSourceRefinement σ q s)).obj 0 = q :=
  (congrArg (fun t : SimplexData A D (n + 2) => t.obj 0)
    (dgGeneralLastHornSourceRefinement_knownData σ q s)).trans
      (dgSourceRefinementObj_zero D (HornData.knownData σ).obj q)

/-- 新ホーンの正番号対象は元の同じ対象。 -/
lemma dgGeneralLastHornSourceRefinement_obj_ne_zero (j : Fin (n + 3)) (hj : j ≠ 0) :
    (HornData.knownData (dgGeneralLastHornSourceRefinement σ q s)).obj j =
      (HornData.knownData σ).obj j :=
  (congrArg (fun t : SimplexData A D (n + 2) => t.obj j)
    (dgGeneralLastHornSourceRefinement_knownData σ q s)).trans
      (dgSourceRefinementObj_ne_zero D (HornData.knownData σ).obj q j hj)

/-- 新ホーンの最後直前の対象は、元の同じ対象。 -/
lemma dgGeneralLastHornSourceRefinement_obj_penultimate :
    (HornData.knownData (dgGeneralLastHornSourceRefinement σ q s)).obj (dgLastHornPenultimate n) =
      (HornData.knownData σ).obj (dgLastHornPenultimate n) :=
  dgGeneralLastHornSourceRefinement_obj_ne_zero σ q s _ (ne_of_gt (dgLastHornPenultimate_pos n))

/-- 新ホーンの終対象は、元の同じ終対象。 -/
lemma dgGeneralLastHornSourceRefinement_obj_last :
    (HornData.knownData (dgGeneralLastHornSourceRefinement σ q s)).obj (Fin.last (n + 2)) =
      (HornData.knownData σ).obj (Fin.last (n + 2)) :=
  dgGeneralLastHornSourceRefinement_obj_ne_zero σ q s _ (by simp)

/-- 新ホーンの欠面右辺 R は、元の同じ R の閉前合成。 -/
lemma dgGeneralLastHornSourceRefinement_missingResidual :
    HEq (dgGeneralLastHornMissingResidual (dgGeneralLastHornSourceRefinement σ q s))
      (dgGradedPrecompose A D (-(n : ℤ) + 1) (dgGeneralLastHornMissingResidual σ) s) :=
  (SimplexData.rhs_heq_of_eq (dgGeneralLastHornSourceRefinement_knownData σ q s)
    (dgLastHornMissingIndex n) 0 (dgLastHornPenultimate n) (-(n : ℤ))
    (dgLastHornMissingIndex_two n) (dgLastHornMissingIndex_min n)
    (dgLastHornMissingIndex_max n) (dgLastHornMissingIndex_degree n)).trans
      (dgSimplexDataInitialRefinement_rhs_from_zero A D (HornData.knownData σ) q s
        _ _ _ _ _ _ _)

/-- 新ホーンの最上位既知残差 K は、元の同じ K の閉前合成。 -/
lemma dgGeneralLastHornSourceRefinement_topResidual :
    HEq (dgGeneralLastHornTopResidual (dgGeneralLastHornSourceRefinement σ q s))
      (dgGradedPrecompose A D (-(n : ℤ) - 1 + 1) (dgGeneralLastHornTopResidual σ) s) :=
  (SimplexData.rhs_heq_of_eq (dgGeneralLastHornSourceRefinement_knownData σ q s)
    Finset.univ 0 (Fin.last (n + 2)) (-(n : ℤ) - 1) (dgLastHornTop_two n)
    (dgLastHornTop_min n) (dgLastHornTop_max n) (dgLastHornTop_degree n)).trans
      (dgSimplexDataInitialRefinement_rhs_from_zero A D (HornData.knownData σ) q s
        _ _ _ _ _ _ _)

/-- 新ホーンの実最後辺は、元の最後辺を厳密に保つ。 -/
lemma dgGeneralLastHornSourceRefinement_lastEdge :
    HEq ((HornData.knownData (dgGeneralLastHornSourceRefinement σ q s)).edgeHom
      (dgLastHornPenultimate n) (Fin.last (n + 2)) (dgLastHornPenultimate_lt_last n))
      ((HornData.knownData σ).edgeHom (dgLastHornPenultimate n) (Fin.last (n + 2))
        (dgLastHornPenultimate_lt_last n)) := by
  unfold SimplexData.edgeHom
  apply (SimplexData.hom_heq_of_eq (dgGeneralLastHornSourceRefinement_knownData σ q s)
    _ _ _ _ _ _ _ _).trans
  exact dgSimplexDataInitialRefinement_hom_ne_zero A D (HornData.knownData σ) q s
    _ _ _ _ _ _ _ _ (ne_of_gt (dgLastHornPenultimate_pos n))

end SerrePositivity.InfinityCategories
