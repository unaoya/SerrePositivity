module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.JoinInitialVertexDetection
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.JoinHornFaceGeometry

/-!
概要：切断一の外ホーンから join への射の検出。
方針：零以外の面は始点を共有し、右因子を保つ joinMap の像と合わせて各面を検査する。
規約：欠けた面は零番目、ホーンの次元は n+2。
使われ方：Kerodon Proposition 5.2.3.15（Tag 024J）、相対 join の cocartesian 辺の外ホーン充填。

対応節は Kerodon 5.2（Tag 019A）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport

/-- 概要：切断一の標準単体から join への射は始点と joinMap の像から決まる。
方針：Yoneda の自然性により単体の検出へ帰着する。
規約：右因子を保つ joinMap の左因子には単射性を要求しない。
使われ方：Kerodon Proposition 5.2.3.15（Tag 024J）、外ホーンの各面の比較。 -/
lemma join_hom_ext_of_initial_vertex_joinMap {X X' Y : SSet.{u}} (n : ℕ)
    (f : X ⟶ X') {a b : (Δ[n] : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join X Y}
    (ha : (SSet.yonedaEquiv a).1.val = 1) (hb : (SSet.yonedaEquiv b).1.val = 1)
    (h0 : stdSimplex.map (SimplexCategory.const ⦋0⦌ ⦋n⦌ 0) ≫ a =
      stdSimplex.map (SimplexCategory.const ⦋0⦌ ⦋n⦌ 0) ≫ b)
    (hf : a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap f (𝟙 Y) = b ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap f (𝟙 Y)) : a = b := by
  have he0 := congrArg SSet.yonedaEquiv h0
  rw [← SSet.yonedaEquiv_naturality, ← SSet.yonedaEquiv_naturality] at he0
  have hef := congrArg SSet.yonedaEquiv hf
  rw [SSet.yonedaEquiv_comp, SSet.yonedaEquiv_comp] at hef
  apply SSet.yonedaEquiv.injective
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.Join.Simplex.ext_of_initial_vertex_joinMap f _ _ ha hb he0 hef

/-- 概要：零以外の頂点を除く面は切断一を保つ。
方針：最初の頂点が保たれることと、他の頂点が零に写らないことを使う。
規約：面の次元は n+1。
使われ方：Kerodon Proposition 5.2.3.15（Tag 024J）、外ホーンの各面の切断の計算。 -/
lemma Join.pullCut_delta_one_of_ne_zero (n : ℕ) (j : Fin (n + 3)) (hj : j ≠ 0) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.pullCut (SimplexCategory.δ j).toOrderHom 1 = 1 := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.cut_ext (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.pullCut_le _ _) (by omega)
  intro i
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.lt_pullCut_iff]
  change (j.succAbove i).val < 1 ↔ i.val < 1
  by_cases hi : i = 0
  · subst i
    rw [Fin.succAbove_ne_zero_zero hj]
    simp
  · have hi' : 0 < i.val := by have := Fin.pos_iff_ne_zero.mpr hi; exact this
    simp only [Fin.succAbove]
    split_ifs <;> simp only [Fin.val_castSucc, Fin.val_succ] <;> omega

/-- 概要：零番目の外ホーンの全ての面は同じ始点を持つ。
方針：ホーン包含の単射性で標準単体の始点の等式へ戻す。
規約：比較の基準は最後の面の始点。
使われ方：Kerodon Proposition 5.2.3.15（Tag 024J）、外ホーンの左因子の整合性。 -/
lemma initialHorn_face_initial_vertex (n : ℕ) (j : Fin (n + 3)) (hj : j ≠ 0) :
    stdSimplex.map (SimplexCategory.const ⦋0⦌ ⦋n + 1⦌ 0) ≫ horn.ι 0 j hj =
      stdSimplex.map (SimplexCategory.const ⦋0⦌ ⦋n + 1⦌ 0) ≫
        horn.ι (0 : Fin (n + 3)) (Fin.last (n + 2)) (by simp) := by
  apply (cancel_mono (horn (n + 2) 0).ι).1
  simp only [Category.assoc, horn.ι_ι]
  apply SSet.yonedaEquiv.injective
  apply stdSimplex.ext
  intro i
  change j.succAbove 0 = (Fin.last (n + 2)).succAbove 0
  rw [Fin.succAbove_ne_zero_zero hj, Fin.succAbove_ne_zero_zero (by simp)]

/-- 概要：切断一の外ホーンから join への二射は共通の始点と joinMap の像で決まる。
方針：各面の切断と始点を同定し、標準単体の検出補題を使う。
規約：時間の射はホーン全体の標準単体上で指定する。
使われ方：Kerodon Proposition 5.2.3.15（Tag 024J）、相対 join の充填が元の外ホーンを延長することの検査。 -/
lemma join_initialHorn_hom_ext_of_initial_vertex_joinMap {X X' Y : SSet.{u}} (n : ℕ)
    (f : X ⟶ X') (a b : (horn (n + 2) 0 : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join X Y)
    (t : (Δ[n + 2] : SSet.{u}) ⟶ Δ[1])
    (hat : (horn (n + 2) 0).ι ≫ t = a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinIntervalProjection X Y)
    (hbt : (horn (n + 2) 0).ι ≫ t = b ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinIntervalProjection X Y)
    (ht : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.pullCut (stdSimplex.objEquiv (SSet.yonedaEquiv t)).toOrderHom 1 = 1)
    (h0 : (stdSimplex.map (SimplexCategory.const ⦋0⦌ ⦋n + 1⦌ 0) ≫
      horn.ι (0 : Fin (n + 3)) (Fin.last (n + 2)) (by simp)) ≫ a =
      (stdSimplex.map (SimplexCategory.const ⦋0⦌ ⦋n + 1⦌ 0) ≫
        horn.ι (0 : Fin (n + 3)) (Fin.last (n + 2)) (by simp)) ≫ b)
    (hf : a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap f (𝟙 Y) = b ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap f (𝟙 Y)) : a = b := by
  apply horn.hom_ext
  intro j hj
  have he : horn.ι 0 j hj ≫ a = horn.ι 0 j hj ≫ b := by
    apply join_hom_ext_of_initial_vertex_joinMap (n + 1) f
    · rw [SSet.yonedaEquiv_comp, horn.yonedaEquiv_ι, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join_horn_face_cut n 0 a t hat, ht]
      exact Join.pullCut_delta_one_of_ne_zero n j hj
    · rw [SSet.yonedaEquiv_comp, horn.yonedaEquiv_ι, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join_horn_face_cut n 0 b t hbt, ht]
      exact Join.pullCut_delta_one_of_ne_zero n j hj
    · simpa only [← Category.assoc, initialHorn_face_initial_vertex n j hj] using h0
    · simpa only [Category.assoc] using congrArg (fun q ↦ horn.ι 0 j hj ≫ q) hf
  have hh := congrArg SSet.yonedaEquiv he
  simpa only [SSet.yonedaEquiv_comp, horn.yonedaEquiv_ι] using hh

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport
