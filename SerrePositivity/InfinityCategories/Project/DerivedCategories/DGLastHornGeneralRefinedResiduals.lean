module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGLastHornGeneralRefinedData
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGLastHornGeneralFinalEdge
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGInitialRefinementComponents
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.DataRhsComponents

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
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
open scoped _root_.Simplicial
variable {A : Type u} [CommRing A] {D : Type v} [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] {n : ℕ}
variable (σ : (Λ[n + 2, Fin.last (n + 2)] : SSet.{max u v}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D) (q : D)
variable (s : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) q ⟶
  ForgetEnrichment.of (Complex A) ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).obj 0))

/-- 新ホーンの始対象は、同じ指定細分対象 q。 -/
lemma dgGeneralLastHornSourceRefinement_obj_zero :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGeneralLastHornSourceRefinement σ q s)).obj 0 = q :=
  (congrArg (fun t : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D (n + 2) => t.obj 0)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGeneralLastHornSourceRefinement_knownData σ q s)).trans
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSourceRefinementObj_zero D (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).obj q)

/-- 新ホーンの正番号対象は元の同じ対象。 -/
lemma dgGeneralLastHornSourceRefinement_obj_ne_zero (j : Fin (n + 3)) (hj : j ≠ 0) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGeneralLastHornSourceRefinement σ q s)).obj j =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).obj j :=
  (congrArg (fun t : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D (n + 2) => t.obj j)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGeneralLastHornSourceRefinement_knownData σ q s)).trans
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSourceRefinementObj_ne_zero D (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).obj q j hj)

/-- 新ホーンの最後直前の対象は、元の同じ対象。 -/
lemma dgGeneralLastHornSourceRefinement_obj_penultimate :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGeneralLastHornSourceRefinement σ q s)).obj (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornPenultimate n) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).obj (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornPenultimate n) :=
  dgGeneralLastHornSourceRefinement_obj_ne_zero σ q s _ (ne_of_gt (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornPenultimate_pos n))

/-- 新ホーンの終対象は、元の同じ終対象。 -/
lemma dgGeneralLastHornSourceRefinement_obj_last :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGeneralLastHornSourceRefinement σ q s)).obj (Fin.last (n + 2)) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).obj (Fin.last (n + 2)) :=
  dgGeneralLastHornSourceRefinement_obj_ne_zero σ q s _ (by simp)

/-- 新ホーンの欠面右辺 R は、元の同じ R の閉前合成。 -/
lemma dgGeneralLastHornSourceRefinement_missingResidual :
    HEq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGeneralLastHornMissingResidual (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGeneralLastHornSourceRefinement σ q s))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGradedPrecompose A D (-(n : ℤ) + 1) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGeneralLastHornMissingResidual σ) s) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.rhs_heq_of_eq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGeneralLastHornSourceRefinement_knownData σ q s)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornMissingIndex n) 0 (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornPenultimate n) (-(n : ℤ))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornMissingIndex_two n) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornMissingIndex_min n)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornMissingIndex_max n) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornMissingIndex_degree n)).trans
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSimplexDataInitialRefinement_rhs_from_zero A D (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ) q s
        _ _ _ _ _ _ _)

/-- 新ホーンの最上位既知残差 K は、元の同じ K の閉前合成。 -/
lemma dgGeneralLastHornSourceRefinement_topResidual :
    HEq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGeneralLastHornTopResidual (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGeneralLastHornSourceRefinement σ q s))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGradedPrecompose A D (-(n : ℤ) - 1 + 1) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGeneralLastHornTopResidual σ) s) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.rhs_heq_of_eq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGeneralLastHornSourceRefinement_knownData σ q s)
    Finset.univ 0 (Fin.last (n + 2)) (-(n : ℤ) - 1) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornTop_two n)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornTop_min n) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornTop_max n) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornTop_degree n)).trans
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSimplexDataInitialRefinement_rhs_from_zero A D (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ) q s
        _ _ _ _ _ _ _)

/-- 新ホーンの実最後辺は、元の最後辺を厳密に保つ。 -/
lemma dgGeneralLastHornSourceRefinement_lastEdge :
    HEq ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGeneralLastHornSourceRefinement σ q s)).edgeHom
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornPenultimate n) (Fin.last (n + 2)) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornPenultimate_lt_last n))
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).edgeHom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornPenultimate n) (Fin.last (n + 2))
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornPenultimate_lt_last n)) := by
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData.edgeHom
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.hom_heq_of_eq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGeneralLastHornSourceRefinement_knownData σ q s)
    _ _ _ _ _ _ _ _).trans
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSimplexDataInitialRefinement_hom_ne_zero A D (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ) q s
    _ _ _ _ _ _ _ _ (ne_of_gt (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornPenultimate_pos n))

end SerrePositivity.InfinityCategories.Project.DerivedCategories
