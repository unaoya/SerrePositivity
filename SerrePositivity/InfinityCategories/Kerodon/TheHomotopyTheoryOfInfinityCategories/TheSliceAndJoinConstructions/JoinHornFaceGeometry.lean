module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.JoinMixedHornDetection

/-!
概要：join の内ホーンにおける切断と両端の面の整合性。
方針：区間の単体の引き戻しから切断を計算し、単体恒等式をホーンの包含で検査する。
規約：内ホーンの次元は n+2。
使われ方：Kerodon Proposition 4.3.3.24（Tag 02QU）、混合ホーンの充填単体の検査。

対応節は Kerodon 4.3（Tag 015M）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions

/-- 概要：混合切断を持つ単体の内側の面も混合切断を持つ。
方針：最初と最後の頂点が面写像で保たれることを使う。
規約：除く頂点 j は最初・最後のどちらでもない。
使われ方：Kerodon Proposition 4.3.3.24（Tag 02QU）、両端の面による各内側の面の検出。 -/
lemma Join.pullCut_delta_inner_mixed (n l : ℕ) (hl0 : 0 < l) (hl1 : l ≤ n + 2)
    (j : Fin (n + 3)) (hj0 : 0 < j) (hj1 : j < Fin.last (n + 2)) :
    0 < _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.pullCut (SimplexCategory.δ j).toOrderHom l ∧
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.pullCut (SimplexCategory.δ j).toOrderHom l ≤ n + 1 := by
  have h0 := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.lt_pullCut_iff (SimplexCategory.δ j).toOrderHom l (0 : Fin (n + 2))
  have hlast := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.lt_pullCut_iff (SimplexCategory.δ j).toOrderHom l (Fin.last (n + 1))
  change 0 < _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.pullCut (SimplexCategory.δ j).toOrderHom l ↔ (j.succAbove 0).val < l at h0
  change n + 1 < _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.pullCut (SimplexCategory.δ j).toOrderHom l ↔
    (j.succAbove (Fin.last (n + 1))).val < l at hlast
  rw [Fin.succAbove_ne_zero_zero (ne_of_gt hj0)] at h0
  rw [Fin.succAbove_ne_last_last (ne_of_lt hj1)] at hlast
  constructor
  · exact h0.mpr hl0
  · have hn : ¬ n + 1 < _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.pullCut (SimplexCategory.δ j).toOrderHom l := by
      intro h
      have := hlast.mp h
      change n + 2 < l at this
      omega
    omega

/-- 概要：区間を保つホーンの射の各面の切断は区間の単体の切断の引き戻し。
方針：面に制限した射を Yoneda で評価し、切断の合成則を使う。
規約：t は標準単体全体で指定した時間の射。
使われ方：Kerodon Proposition 4.3.3.24（Tag 02QU）、両端の面の貼り合わせの切断条件。 -/
lemma join_horn_face_cut {X Y : SSet.{u}} (n : ℕ) (i : Fin (n + 3))
    (a : (horn (n + 2) i : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join X Y) (t : (Δ[n + 2] : SSet.{u}) ⟶ Δ[1])
    (ht : (horn (n + 2) i).ι ≫ t = a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinIntervalProjection X Y)
    (j : Fin (n + 3)) (hj : j ≠ i) :
    (a.app (Opposite.op ⦋n + 1⦌) (horn.face i j hj)).1.val =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.pullCut (SimplexCategory.δ j).toOrderHom
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.pullCut (stdSimplex.objEquiv (SSet.yonedaEquiv t)).toOrderHom 1) := by
  have hm : (horn.ι i j hj ≫ a) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinIntervalProjection X Y = stdSimplex.δ j ≫ t := by
    rw [Category.assoc, ← ht, ← Category.assoc, horn.ι_ι]
  have he := congrArg SSet.yonedaEquiv hm
  rw [SSet.yonedaEquiv_comp (horn.ι i j hj ≫ a), SSet.yonedaEquiv_comp (horn.ι i j hj),
    horn.yonedaEquiv_ι, stdSimplex.yonedaEquiv_δ_comp] at he
  have hc := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinIntervalProjection_app_cut X Y (n + 1) (a.app _ (horn.face i j hj))
  rw [he] at hc
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.pullCut ((stdSimplex.objEquiv (SSet.yonedaEquiv t)).toOrderHom.comp
    (SimplexCategory.δ j).toOrderHom) 1 = _ at hc
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.pullCut_comp] at hc
  exact hc.symm

/-- 概要：ホーンの内側の面の最初の面は、ホーンの最初の面を経由する。
方針：ホーン包含の単射性で通常の単体恒等式へ戻す。
規約：i と j は零でなく、j は欠けた面ではない。
使われ方：Kerodon Proposition 4.3.3.24（Tag 02QU）、内側の面の左端の整合性。 -/
lemma horn_inner_face_zero_comp (n : ℕ) (i j : Fin (n + 3)) (hi0 : 0 < i) (hj0 : 0 < j)
    (hji : j ≠ i) :
    stdSimplex.δ (0 : Fin (n + 2)) ≫ horn.ι i j hji =
      stdSimplex.δ (j.pred (ne_of_gt hj0)) ≫ horn.ι i 0 (ne_of_gt hi0).symm := by
  apply (cancel_mono (horn (n + 2) i).ι).1
  simp only [Category.assoc, horn.ι_ι]
  have hd := stdSimplex.δ_comp_δ' (i := (0 : Fin (n + 2))) (j := j) hj0
  have hz : (0 : Fin (n + 2)).castSucc = (0 : Fin (n + 3)) := Fin.ext rfl
  simpa only [hz] using hd

/-- 概要：ホーンの内側の面の最後の面は、ホーンの最後の面を経由する。
方針：ホーン包含の単射性で通常の単体恒等式へ戻す。
規約：i と j は最後の頂点でなく、j は欠けた面ではない。
使われ方：Kerodon Proposition 4.3.3.24（Tag 02QU）、内側の面の右端の整合性。 -/
lemma horn_inner_face_last_comp (n : ℕ) (i j : Fin (n + 3))
    (hi1 : i < Fin.last (n + 2)) (hj1 : j < Fin.last (n + 2)) (hji : j ≠ i) :
    stdSimplex.δ (Fin.last (n + 1)) ≫ horn.ι i j hji =
      stdSimplex.δ (j.castPred (ne_of_lt hj1)) ≫ horn.ι i (Fin.last (n + 2)) (ne_of_gt hi1) := by
  apply (cancel_mono (horn (n + 2) i).ι).1
  simp only [Category.assoc, horn.ι_ι]
  simpa only [Fin.succ_last, Fin.castSucc_castPred] using
    (stdSimplex.δ_comp_δ (Fin.le_last (j.castPred (ne_of_lt hj1)))).symm

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
