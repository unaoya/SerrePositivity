module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.JoinExtremeFaceGluing
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.JoinMixedHornUniqueness
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.IntervalCutDetection

/-!
概要：混合した時間を持つ join の内ホーンは一意に充填できる。
方針：最初・最後の面を貼り、時間の切断とホーン上の一意性で全体を比較する。
規約：左右の因子の quasicategory 性は混合の場合には要求しない。
使われ方：Kerodon Proposition 4.3.3.24（Tag 02QU）、quasicategory の join の充填の混合分岐。

対応節は Kerodon 4.3（Tag 015M）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions

/-- 概要：内ホーンの混合した時間の延長を固定すると join への射を充填できる。
方針：両端の面の切断と共通の面の整合性を検査し、両因子の単体を貼り合わせる。
規約：充填は時間の射 t を保つ。
使われ方：Kerodon Proposition 4.3.3.24（Tag 02QU）、通常の join の内ホーンの充填。 -/
lemma join_mixed_innerHorn_filling {X Y : SSet.{u}} (n : ℕ) (i : Fin (n + 3))
    (hi0 : 0 < i) (hi1 : i < Fin.last (n + 2))
    (a : (horn (n + 2) i : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join X Y) (t : (Δ[n + 2] : SSet.{u}) ⟶ Δ[1])
    (ht : (horn (n + 2) i).ι ≫ t = a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinIntervalProjection X Y)
    (ht0 : 0 < _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.pullCut (stdSimplex.objEquiv (SSet.yonedaEquiv t)).toOrderHom 1)
    (ht1 : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.pullCut (stdSimplex.objEquiv (SSet.yonedaEquiv t)).toOrderHom 1 ≤ n + 2) :
    ∃ l : (Δ[n + 2] : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join X Y,
      (horn (n + 2) i).ι ≫ l = a ∧ l ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinIntervalProjection X Y = t := by
  let C := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.pullCut (stdSimplex.objEquiv (SSet.yonedaEquiv t)).toOrderHom 1
  let u0 := horn.ι i 0 (ne_of_gt hi0).symm
  let u1 := horn.ι i (Fin.last (n + 2)) (ne_of_gt hi1)
  let a0 := a.app (Opposite.op ⦋n + 1⦌) (horn.face i 0 (ne_of_gt hi0).symm)
  let a1 := a.app (Opposite.op ⦋n + 1⦌) (horn.face i (Fin.last (n + 2)) (ne_of_gt hi1))
  have ha0 : SSet.yonedaEquiv (u0 ≫ a) = a0 := by
    rw [SSet.yonedaEquiv_comp, horn.yonedaEquiv_ι]
  have ha1 : SSet.yonedaEquiv (u1 ≫ a) = a1 := by
    rw [SSet.yonedaEquiv_comp, horn.yonedaEquiv_ι]
  have hc0 : a0.1.val = C - 1 := by
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join_horn_face_cut n i a t ht 0 (ne_of_gt hi0).symm]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.Join.pullCut_delta_zero (n + 1) C ht0 (by omega)
  have hc1 : a1.1.val = C := by
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join_horn_face_cut n i a t ht (Fin.last (n + 2)) (ne_of_gt hi1)]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.Join.pullCut_delta_last (n + 1) C ht1
  have hfaces : stdSimplex.δ (Fin.last (n + 1)) ≫ u0 = stdSimplex.δ (0 : Fin (n + 2)) ≫ u1 := by
    have he := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.horn_inner_face_zero_comp n i (Fin.last (n + 2)) hi0 (by change (0 : ℕ) < n + 2; omega) (ne_of_gt hi1)
    simpa only [Fin.pred_last] using he.symm
  have hab := congrArg (fun q ↦ SSet.yonedaEquiv (q ≫ a)) hfaces
  rw [Category.assoc, Category.assoc, stdSimplex.yonedaEquiv_δ_comp,
    stdSimplex.yonedaEquiv_δ_comp, ha0, ha1] at hab
  obtain ⟨s, hsc, hs0, hs1⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.Simplex.exists_extreme_faces a0 a1 (by omega) hab
  let l : (Δ[n + 2] : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join X Y := SSet.yonedaEquiv.symm s
  have hlt : l ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinIntervalProjection X Y = t := by
    apply SSet.yonedaEquiv.injective
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.intervalSimplex_eq_of_pullCut_eq
    rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinIntervalProjection_app_cut]
    exact hsc.trans hc1
  have hl0 : stdSimplex.δ (0 : Fin (n + 3)) ≫ l = u0 ≫ a := by
    apply SSet.yonedaEquiv.injective
    rw [stdSimplex.yonedaEquiv_δ_comp, Equiv.apply_symm_apply, ha0]
    exact hs0
  have hl1 : stdSimplex.δ (Fin.last (n + 2)) ≫ l = u1 ≫ a := by
    apply SSet.yonedaEquiv.injective
    rw [stdSimplex.yonedaEquiv_δ_comp, Equiv.apply_symm_apply, ha1]
    exact hs1
  refine ⟨l, ?_, hlt⟩
  have hft : (horn (n + 2) i).ι ≫ t =
      ((horn (n + 2) i).ι ≫ l) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinIntervalProjection X Y := by rw [Category.assoc, hlt]
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join_horn_hom_ext_extreme_faces n i hi0 hi1 _ a t hft ht ht0 ht1
  · rw [← Category.assoc, horn.ι_ι]
    exact hl0
  · rw [← Category.assoc, horn.ι_ι]
    exact hl1

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
