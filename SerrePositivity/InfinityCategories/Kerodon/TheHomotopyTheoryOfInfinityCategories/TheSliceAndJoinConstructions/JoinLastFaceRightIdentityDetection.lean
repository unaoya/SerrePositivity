module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.JoinRightIdentityPreimage
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.JoinHornFaceGeometry

/-!
概要：右因子を保つ joinMap の像と最後の面で混合単体・左ホーンを検出する。
方針：最後の面が保つ左因子と像が保つ右因子を合わせる。
規約：ホーンの欠けた面が最後でないことを要求する。
使われ方：relative arrow collage の left fibration 性の混合分岐。

対応節は Kerodon 4.3（Tag 015M）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions

/-- 概要：右因子を保つ像と最後の面から非左定値の単体への射を検出する。
方針：最後の面の左因子の保存と joinMap による右因子の保存を使う。
規約：右因子を含む切断を仮定する。
使われ方：混合ホーンの各面の検査。 -/
lemma join_hom_ext_last_face_right_id {X X' Y : SSet.{u}} (n : ℕ) (f : X ⟶ X')
    {a b : (Δ[n + 1] : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join X Y}
    (ha : (SSet.yonedaEquiv a).1.val ≤ n + 1)
    (hb : (SSet.yonedaEquiv b).1.val ≤ n + 1)
    (hlast : stdSimplex.δ (Fin.last (n + 1)) ≫ a =
      stdSimplex.δ (Fin.last (n + 1)) ≫ b)
    (him : a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap f (𝟙 Y) = b ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap f (𝟙 Y)) : a = b := by
  have hf := congrArg SSet.yonedaEquiv hlast
  rw [stdSimplex.yonedaEquiv_δ_comp, stdSimplex.yonedaEquiv_δ_comp] at hf
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.simplexMap X Y (SimplexCategory.δ (Fin.last (n + 1))).toOrderHom
    (SSet.yonedaEquiv a) = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.simplexMap X Y
      (SimplexCategory.δ (Fin.last (n + 1))).toOrderHom (SSet.yonedaEquiv b) at hf
  have hx : HEq
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.simplexMap X Y (SimplexCategory.δ (Fin.last (n + 1))).toOrderHom
        (SSet.yonedaEquiv a)).2.1
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.simplexMap X Y (SimplexCategory.δ (Fin.last (n + 1))).toOrderHom
        (SSet.yonedaEquiv b)).2.1 := by rw [hf]
  apply SSet.yonedaEquiv.injective
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.Join.Simplex.ext_of_joinMap_right_id f
  · exact (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.Join.simplexMap_delta_last_left_heq _ ha).symm.trans
      (hx.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.Join.simplexMap_delta_last_left_heq _ hb))
  · simpa only [SSet.yonedaEquiv_comp] using congrArg SSet.yonedaEquiv him

/-- 概要：同じ混合時間の左ホーンは最後の面と右因子を保つ像で決まる。
方針：最後以外の面をさらに最後の面へ制限して検査する。
規約：零番目の外ホーンを含み欠けた面は最後以外。
使われ方：全ての左ホーンの混合充填の境界等式。 -/
lemma join_horn_hom_ext_last_face_right_id {X X' Y : SSet.{u}} (n : ℕ)
    (i : Fin (n + 3)) (hi : i < Fin.last (n + 2)) (f : X ⟶ X')
    (a b : (horn (n + 2) i : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join X Y)
    (t : (Δ[n + 2] : SSet.{u}) ⟶ Δ[1])
    (hat : (horn (n + 2) i).ι ≫ t = a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinIntervalProjection X Y)
    (hbt : (horn (n + 2) i).ι ≫ t = b ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinIntervalProjection X Y)
    (ht0 : 0 < _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.pullCut (stdSimplex.objEquiv (SSet.yonedaEquiv t)).toOrderHom 1)
    (ht1 : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.pullCut (stdSimplex.objEquiv (SSet.yonedaEquiv t)).toOrderHom 1 ≤ n + 2)
    (hlast : horn.ι i (Fin.last (n + 2)) (ne_of_gt hi) ≫ a =
      horn.ι i (Fin.last (n + 2)) (ne_of_gt hi) ≫ b)
    (him : a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap f (𝟙 Y) = b ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap f (𝟙 Y)) : a = b := by
  apply horn.hom_ext
  intro j hji
  have heq : horn.ι i j hji ≫ a = horn.ι i j hji ≫ b := by
    by_cases hj : j = Fin.last (n + 2)
    · subst j
      exact hlast
    have hjlast : j < Fin.last (n + 2) := Fin.lt_last_iff_ne_last.mpr hj
    have hcut : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.pullCut (SimplexCategory.δ j).toOrderHom
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.pullCut (stdSimplex.objEquiv (SSet.yonedaEquiv t)).toOrderHom 1) ≤ n + 1 := by
      by_cases hj0 : j = 0
      · subst j
        rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.Join.pullCut_delta_zero (n + 1) _ ht0 (by omega)]
        omega
      · exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.pullCut_delta_inner_mixed n _ ht0 ht1 j
          (Fin.pos_iff_ne_zero.mpr hj0) hjlast).2
    apply join_hom_ext_last_face_right_id n f
    · rw [SSet.yonedaEquiv_comp, horn.yonedaEquiv_ι, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join_horn_face_cut n i a t hat]
      exact hcut
    · rw [SSet.yonedaEquiv_comp, horn.yonedaEquiv_ι, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join_horn_face_cut n i b t hbt]
      exact hcut
    · rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.horn_inner_face_last_comp n i j hi hjlast hji,
        Category.assoc, hlast, ← Category.assoc,
        ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.horn_inner_face_last_comp n i j hi hjlast hji, Category.assoc]
    · simp only [Category.assoc, him]
  simpa only [SSet.yonedaEquiv_comp, horn.yonedaEquiv_ι] using congrArg SSet.yonedaEquiv heq


end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
