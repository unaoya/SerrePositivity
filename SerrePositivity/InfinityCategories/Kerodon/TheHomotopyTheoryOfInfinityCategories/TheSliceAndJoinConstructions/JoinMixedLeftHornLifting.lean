module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.JoinLastFaceRightIdentityDetection
public import Mathlib.AlgebraicTopology.SimplicialSet.HornColimits

/-!
概要：右因子を保つ joinMap の混合した左ホーンの持ち上げ。
方針：最後の面の左因子と指定像の右因子から候補を作り検出補題で境界を検査する。
規約：零番目のホーンを含み最後のホーンを除く。
使われ方：relative arrow collage の混合分岐の left fibration 性。

対応節は Kerodon 4.3（Tag 015M）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions

/-- 概要：混合した指定像への左ホーンは右因子を保つ joinMap に沿って持ち上がる。
方針：最後の面から回収した左因子で指定像の逆像を作る。
規約：因子の Kan 性や射の充填性は不要。
使われ方：終域側で充填した係数を相対射の全空間へ戻す。 -/
lemma joinMap_right_id_mixed_leftHorn_hasLift {X X' Y : SSet.{u}} (n : ℕ)
    (i : Fin (n + 3)) (hi : i < Fin.last (n + 2)) (f : X ⟶ X')
    (a : (horn (n + 2) i : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join X Y)
    (b : (Δ[n + 2] : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join X' Y)
    (hsq : (horn (n + 2) i).ι ≫ b = a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap f (𝟙 Y))
    (hb0 : 0 < (SSet.yonedaEquiv b).1.val) (hb1 : (SSet.yonedaEquiv b).1.val ≤ n + 2) :
    ∃ l : (Δ[n + 2] : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join X Y,
      (horn (n + 2) i).ι ≫ l = a ∧ l ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap f (𝟙 Y) = b := by
  let t := b ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinIntervalProjection X' Y
  have htcut : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.pullCut (stdSimplex.objEquiv (SSet.yonedaEquiv t)).toOrderHom 1 =
      (SSet.yonedaEquiv b).1.val := by
    rw [SSet.yonedaEquiv_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinIntervalProjection_app_cut]
  have hat : (horn (n + 2) i).ι ≫ t = a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinIntervalProjection X Y := by
    change ((horn (n + 2) i).ι ≫ b) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinIntervalProjection X' Y = _
    rw [hsq, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinIntervalProjection_naturality]
  let u := horn.ι i (Fin.last (n + 2)) (ne_of_gt hi)
  let v := a.app (Opposite.op ⦋n + 1⦌) (horn.face i (Fin.last (n + 2)) (ne_of_gt hi))
  have hv : v.1.val = (SSet.yonedaEquiv b).1.val := by
    change (a.app _ (horn.face _ _ _)).1.val = _
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join_horn_face_cut n i a t hat, htcut, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.Join.pullCut_delta_last (n + 1) _ hb1]
  have hface : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap f (𝟙 Y)).app (Opposite.op ⦋n + 1⦌) v =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.simplexMap X' Y (SimplexCategory.δ (Fin.last (n + 2))).toOrderHom
        (SSet.yonedaEquiv b) := by
    have he := congrArg (fun q ↦ u ≫ q) hsq
    dsimp only [u] at he
    rw [← Category.assoc, horn.ι_ι] at he
    rw [← Category.assoc] at he
    have hh := congrArg SSet.yonedaEquiv he
    rw [stdSimplex.yonedaEquiv_δ_comp, SSet.yonedaEquiv_comp,
      SSet.yonedaEquiv_comp, horn.yonedaEquiv_ι] at hh
    exact hh.symm
  obtain ⟨s, hs, hsx, hsb⟩ :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.Simplex.exists_preimage_right_id_of_last_face f (SSet.yonedaEquiv b) hb1 v hv hface
  let l : (Δ[n + 2] : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join X Y := SSet.yonedaEquiv.symm s
  have hlmap : l ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap f (𝟙 Y) = b := by
    apply SSet.yonedaEquiv.injective
    simpa only [l, SSet.yonedaEquiv_comp, Equiv.apply_symm_apply] using hsb
  have hlt : l ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinIntervalProjection X Y = t := by
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinIntervalProjection_naturality f (𝟙 Y), ← Category.assoc, hlmap]
  have himlast : (stdSimplex.δ (Fin.last (n + 2)) ≫ l) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap f (𝟙 Y) =
      (u ≫ a) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap f (𝟙 Y) := by
    rw [Category.assoc, hlmap, Category.assoc, ← hsq, ← Category.assoc, horn.ι_ι]
  have hlast : stdSimplex.δ (Fin.last (n + 2)) ≫ l = u ≫ a := by
    apply SSet.yonedaEquiv.injective
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.Join.Simplex.ext_of_joinMap_right_id f
    · rw [stdSimplex.yonedaEquiv_δ_comp, Equiv.apply_symm_apply,
        SSet.yonedaEquiv_comp, horn.yonedaEquiv_ι]
      exact (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.Join.simplexMap_delta_last_left_heq s (by rw [hs]; exact hb1)).trans hsx
    · simpa only [SSet.yonedaEquiv_comp] using congrArg SSet.yonedaEquiv himlast
  refine ⟨l, ?_, hlmap⟩
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join_horn_hom_ext_last_face_right_id n i hi f _ a t
  · rw [Category.assoc, hlt]
  · exact hat
  · rw [htcut]
    exact hb0
  · rw [htcut]
    exact hb1
  · rw [← Category.assoc, horn.ι_ι]
    exact hlast
  · rw [Category.assoc, hlmap, hsq]

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
