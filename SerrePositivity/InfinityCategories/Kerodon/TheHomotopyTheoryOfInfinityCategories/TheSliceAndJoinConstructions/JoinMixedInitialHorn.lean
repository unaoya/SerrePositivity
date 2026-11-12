module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.JoinInitialHornLastFace

/-!
概要：混合した最初の外ホーンを右恒等の joinMap に沿って充填する。
方針：最後の面の左係数と像の右係数を組にし、最後の面で境界を検出する。
規約：左因子の射と両因子の単体集合は任意。
使われ方：相対 join の底上の cocartesian 辺の充填。

対応節は Kerodon 4.3（Tag 015M）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions

/-- 概要：混合した指定単体に写る最初の外ホーンは右恒等の joinMap に沿って充填できる。
方針：最後の面に残る左係数を使い、右係数は像の単体から取る。
規約：f の fibration 性を要求しない。
使われ方：joinMap の cocartesian 性の混合分岐。 -/
lemma joinMap_right_id_initialHorn_hasLift_of_mixed {X X' Y : SSet.{u}} (n : ℕ)
    (f : X ⟶ X') (a : (horn (n + 2) 0 : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join X Y)
    (b : (Δ[n + 2] : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join X' Y)
    (hsq : (horn (n + 2) 0).ι ≫ b = a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap f (𝟙 Y))
    (hb0 : 0 < (SSet.yonedaEquiv b).1.val) (hb1 : (SSet.yonedaEquiv b).1.val ≤ n + 2) :
    ∃ l : (Δ[n + 2] : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join X Y,
      (horn (n + 2) 0).ι ≫ l = a ∧ l ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap f (𝟙 Y) = b := by
  let t := b ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinIntervalProjection X' Y
  have ht : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.pullCut (stdSimplex.objEquiv (SSet.yonedaEquiv t)).toOrderHom 1 =
      (SSet.yonedaEquiv b).1.val := by
    rw [SSet.yonedaEquiv_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinIntervalProjection_app_cut]
  have hat : (horn (n + 2) 0).ι ≫ t = a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinIntervalProjection X Y := by
    change ((horn (n + 2) 0).ι ≫ b) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinIntervalProjection X' Y = _
    rw [hsq, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinIntervalProjection_naturality]
  let v := a.app (Opposite.op ⦋n + 1⦌)
    (horn.face (0 : Fin (n + 3)) (Fin.last (n + 2)) (by simp))
  have hv : v.1.val = (SSet.yonedaEquiv b).1.val := by
    change (a.app _ (horn.face _ _ _)).1.val = (SSet.yonedaEquiv b).1.val
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join_horn_face_cut n 0 a t hat, ht]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.Join.pullCut_delta_last (n + 1) _ hb1
  let x : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augObj X (SSet.yonedaEquiv b).1.val := cast (congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augObj X) hv) v.2.1
  have hface : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap f (𝟙 Y)).app (Opposite.op ⦋n + 1⦌) v =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.simplexMap X' Y (SimplexCategory.δ (Fin.last (n + 2))).toOrderHom
        (SSet.yonedaEquiv b) := by
    have he := congrArg (fun q ↦ horn.ι (0 : Fin (n + 3)) (Fin.last (n + 2)) (by simp) ≫ q) hsq
    simp only [← Category.assoc, horn.ι_ι] at he
    have hh := congrArg SSet.yonedaEquiv he
    rw [stdSimplex.yonedaEquiv_δ_comp] at hh
    rw [SSet.yonedaEquiv_comp, SSet.yonedaEquiv_comp, horn.yonedaEquiv_ι] at hh
    exact hh.symm
  have hx : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augHom f (SSet.yonedaEquiv b).1.val x =
      (SSet.yonedaEquiv b).2.1 := by
    apply eq_of_heq
    have he := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augHom_cast f hv v.2.1
    have hleft : HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augHom f v.1.val v.2.1)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.simplexMap X' Y (SimplexCategory.δ (Fin.last (n + 2))).toOrderHom
          (SSet.yonedaEquiv b)).2.1 := by
      change HEq ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap f (𝟙 Y)).app (Opposite.op ⦋n + 1⦌) v).2.1 _
      rw [hface]
    exact (heq_of_eq he.symm).trans ((cast_heq _ _).trans
      (hleft.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.Join.simplexMap_delta_last_left_heq _ hb1)))
  obtain ⟨s, hs, hsx, hsb⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinSimplex_exists_preimage_of_left f _ x hx
  let l : (Δ[n + 2] : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join X Y := SSet.yonedaEquiv.symm s
  have hl : l ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap f (𝟙 Y) = b := by
    apply SSet.yonedaEquiv.injective
    simpa only [SSet.yonedaEquiv_comp, l, Equiv.apply_symm_apply] using hsb
  have hlt : l ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinIntervalProjection X Y = t := by
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinIntervalProjection_naturality f (𝟙 Y), ← Category.assoc, hl]
  have hlast : stdSimplex.δ (Fin.last (n + 2)) ≫ l =
      horn.ι (0 : Fin (n + 3)) (Fin.last (n + 2)) (by simp) ≫ a := by
    apply SSet.yonedaEquiv.injective
    rw [stdSimplex.yonedaEquiv_δ_comp, Equiv.apply_symm_apply,
      SSet.yonedaEquiv_comp, horn.yonedaEquiv_ι]
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.Join.Simplex.ext_of_joinMap_right_id f
    · exact (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.Join.simplexMap_delta_last_left_heq s (by rw [hs]; exact hb1)).trans
        (hsx.trans (cast_heq _ _))
    · change SSet.yonedaEquiv ((stdSimplex.δ (Fin.last (n + 2)) ≫ l) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap f (𝟙 Y)) = _
      rw [Category.assoc, hl, stdSimplex.yonedaEquiv_δ_comp]
      exact hface.symm
  refine ⟨l, ?_, hl⟩
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInitialHorn_ext_of_last_face_joinMap n f ((horn (n + 2) 0).ι ≫ l) a t
  · rw [Category.assoc, hlt]
  · rw [ht]; exact hb0
  · rw [ht]; exact hb1
  · rw [← Category.assoc, horn.ι_ι, hlast]
  · rw [Category.assoc, hl, hsq]

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
