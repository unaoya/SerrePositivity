module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.JoinHornFaceGeometry

/-!
概要：混合した時間を持つホーンの join への射を両端の面で検出する。
方針：内側の各面も混合であることと、両端の面の単体恒等式を使う。
規約：ホーンの欠けた面は内側。
使われ方：Kerodon Proposition 4.3.3.24（Tag 02QU）、貼り合わせた充填単体がホーン全体を延長することの確認。

対応節は Kerodon 4.3（Tag 015M）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions

/-- 概要：同じ時間を持つ標準単体から join への混合射は最初・最後の面で決まる。
方針：時間から切断を同定し、両端の面から左右の因子を復元する。
規約：標準単体の次元は n+1。
使われ方：Kerodon Proposition 4.3.3.24（Tag 02QU）、ホーンの各内側の面の検出。 -/
lemma join_hom_ext_extreme_faces_of_interval {X Y : SSet.{u}} (n : ℕ)
    {f g : (Δ[n + 1] : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join X Y}
    (ht : f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinIntervalProjection X Y = g ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinIntervalProjection X Y)
    (hs0 : 0 < (SSet.yonedaEquiv f).1.val) (hs1 : (SSet.yonedaEquiv f).1.val ≤ n + 1)
    (h0 : stdSimplex.δ (0 : Fin (n + 2)) ≫ f = stdSimplex.δ (0 : Fin (n + 2)) ≫ g)
    (h1 : stdSimplex.δ (Fin.last (n + 1)) ≫ f = stdSimplex.δ (Fin.last (n + 1)) ≫ g) : f = g := by
  have he := congrArg SSet.yonedaEquiv ht
  rw [SSet.yonedaEquiv_comp, SSet.yonedaEquiv_comp] at he
  have hf := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinIntervalProjection_app_cut X Y (n + 1) (SSet.yonedaEquiv f)
  have hg := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinIntervalProjection_app_cut X Y (n + 1) (SSet.yonedaEquiv g)
  rw [he] at hf
  have he0 := congrArg SSet.yonedaEquiv h0
  have he1 := congrArg SSet.yonedaEquiv h1
  rw [stdSimplex.yonedaEquiv_δ_comp, stdSimplex.yonedaEquiv_δ_comp] at he0 he1
  apply SSet.yonedaEquiv.injective
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.Join.Simplex.ext_of_extreme_faces _ _ (Fin.ext (hf.symm.trans hg)) hs0 hs1 he0 he1

/-- 概要：同じ混合時間を持つ内ホーンから join への二射は最初・最後の面で決まる。
方針：両端以外の面を両端の面で検出し、ホーンの全ての面で比較する。
規約：t は標準単体全体に与えた時間の射。
使われ方：Kerodon Proposition 4.3.3.24（Tag 02QU）、混合ホーンの貼り合わせの確認。 -/
lemma join_horn_hom_ext_extreme_faces {X Y : SSet.{u}} (n : ℕ) (i : Fin (n + 3))
    (hi0 : 0 < i) (hi1 : i < Fin.last (n + 2))
    (f g : (horn (n + 2) i : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join X Y)
    (t : (Δ[n + 2] : SSet.{u}) ⟶ Δ[1])
    (hft : (horn (n + 2) i).ι ≫ t = f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinIntervalProjection X Y)
    (hgt : (horn (n + 2) i).ι ≫ t = g ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinIntervalProjection X Y)
    (ht0 : 0 < _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.pullCut (stdSimplex.objEquiv (SSet.yonedaEquiv t)).toOrderHom 1)
    (ht1 : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.pullCut (stdSimplex.objEquiv (SSet.yonedaEquiv t)).toOrderHom 1 ≤ n + 2)
    (h0 : horn.ι i 0 (ne_of_gt hi0).symm ≫ f = horn.ι i 0 (ne_of_gt hi0).symm ≫ g)
    (h1 : horn.ι i (Fin.last (n + 2)) (ne_of_gt hi1) ≫ f =
      horn.ι i (Fin.last (n + 2)) (ne_of_gt hi1) ≫ g) : f = g := by
  apply horn.hom_ext
  intro j hji
  have heq : horn.ι i j hji ≫ f = horn.ι i j hji ≫ g := by
    by_cases hj0 : j = 0
    · subst j
      exact h0
    by_cases hj1 : j = Fin.last (n + 2)
    · subst j
      exact h1
    have hj0' : 0 < j := Fin.pos_iff_ne_zero.mpr hj0
    have hj1' : j < Fin.last (n + 2) := Fin.lt_last_iff_ne_last.mpr hj1
    have hc := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join_horn_face_cut n i f t hft j hji
    have hm := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.pullCut_delta_inner_mixed n _ ht0 ht1 j hj0' hj1'
    apply join_hom_ext_extreme_faces_of_interval n
    · simp only [Category.assoc, ← hft, ← hgt]
    · rw [SSet.yonedaEquiv_comp, horn.yonedaEquiv_ι, hc]
      exact hm.1
    · rw [SSet.yonedaEquiv_comp, horn.yonedaEquiv_ι, hc]
      exact hm.2
    · simp only [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.horn_inner_face_zero_comp n i j hi0 hj0' hji]
      simpa only [Category.assoc] using
        congrArg (fun q ↦ stdSimplex.δ (j.pred (ne_of_gt hj0')) ≫ q) h0
    · simp only [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.horn_inner_face_last_comp n i j hi1 hj1' hji]
      simpa only [Category.assoc] using
        congrArg (fun q ↦ stdSimplex.δ (j.castPred (ne_of_lt hj1')) ≫ q) h1
  have he := congrArg SSet.yonedaEquiv heq
  simpa only [SSet.yonedaEquiv_comp, horn.yonedaEquiv_ι] using he

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
