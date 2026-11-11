module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.JoinMapLastFace
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.JoinHornFaceGeometry

/-!
概要：混合した最初の外ホーンの射を最後の面と joinMap の像で検出する。
方針：各内側の面を最後の面との共通面で検出する。
規約：右因子を保つ joinMap を使い、左因子の単射性は不要。
使われ方：相対 join の底上の cocartesian 辺の混合外ホーン充填の検証。

対応節は Kerodon 4.3（Tag 015M）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions

/-- 概要：混合時間を持つ最初の外ホーンは最後の面と joinMap の像で一致を判定できる。
方針：内側の各面にも右係数が残り、その最後の面を共通面の恒等式で比較する。
規約：両因子の充填性は要求しない。
使われ方：模型の充填が元の外ホーンに厳密に一致することの確認。 -/
lemma joinInitialHorn_ext_of_last_face_joinMap {X X' Y : SSet.{u}} (n : ℕ)
    (f : X ⟶ X') (a b : (horn (n + 2) 0 : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join X Y)
    (t : (Δ[n + 2] : SSet.{u}) ⟶ Δ[1])
    (hat : (horn (n + 2) 0).ι ≫ t = a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinIntervalProjection X Y)
    (ht0 : 0 < _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.pullCut (stdSimplex.objEquiv (SSet.yonedaEquiv t)).toOrderHom 1)
    (ht1 : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.pullCut (stdSimplex.objEquiv (SSet.yonedaEquiv t)).toOrderHom 1 ≤ n + 2)
    (hlast : horn.ι (0 : Fin (n + 3)) (Fin.last (n + 2)) (by simp) ≫ a =
      horn.ι (0 : Fin (n + 3)) (Fin.last (n + 2)) (by simp) ≫ b)
    (hf : a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap f (𝟙 Y) = b ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap f (𝟙 Y)) : a = b := by
  apply horn.hom_ext
  intro j hj
  have h : horn.ι 0 j hj ≫ a = horn.ι 0 j hj ≫ b := by
    by_cases hlastj : j = Fin.last (n + 2)
    · subst j
      exact hlast
    have hj0 : 0 < j := Fin.pos_iff_ne_zero.mpr hj
    have hj1 : j < Fin.last (n + 2) := Fin.lt_last_iff_ne_last.mpr hlastj
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinHom_ext_of_last_face_joinMap n f
    · rw [SSet.yonedaEquiv_comp, horn.yonedaEquiv_ι, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join_horn_face_cut n 0 a t hat]
      exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.pullCut_delta_inner_mixed n _ ht0 ht1 j hj0 hj1).2
    · have hi : (0 : Fin (n + 3)) < Fin.last (n + 2) := by
        change (0 : ℕ) < n + 2
        omega
      simp only [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.horn_inner_face_last_comp n 0 j hi hj1 hj]
      simpa only [Category.assoc] using
        congrArg (fun z ↦ stdSimplex.δ (j.castPred (ne_of_lt hj1)) ≫ z) hlast
    · simpa only [Category.assoc] using congrArg (fun z ↦ horn.ι 0 j hj ≫ z) hf
  have he := congrArg SSet.yonedaEquiv h
  simpa only [SSet.yonedaEquiv_comp, horn.yonedaEquiv_ι] using he

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
