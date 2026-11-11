module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.JoinInitialHornDetection

/-!
概要：切断一の外ホーンの joinMap に沿う持ち上げ。
方針：最後の面の左因子と指定単体の右因子から充填を作り、始点と像でホーンを検査する。
規約：右因子の射は恒等射、左因子の射は任意。
使われ方：Kerodon Proposition 5.2.3.15（Tag 024J）、相対 join の標準 prism の垂直辺。

対応節は Kerodon 5.2（Tag 019A）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport

/-- 概要：切断一の指定単体に写る外ホーンは joinMap に沿って充填できる。
方針：最後の面の左因子を持ち上げの頂点として使い、全ての面の始点と像を比較する。
規約：単体集合の充填性も左因子の射の単射性も仮定しない。
使われ方：Kerodon Proposition 5.2.3.15（Tag 024J）、係数側の外ホーン充填から相対 join の充填を作る。 -/
lemma joinMap_right_id_initialHorn_hasLift_of_cut_one {X X' Y : SSet.{u}} (n : ℕ)
    (f : X ⟶ X') (a : (horn (n + 2) 0 : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join X Y)
    (b : (Δ[n + 2] : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join X' Y)
    (hsq : (horn (n + 2) 0).ι ≫ b = a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap f (𝟙 Y))
    (hb : (SSet.yonedaEquiv b).1.val = 1) :
    ∃ l : (Δ[n + 2] : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join X Y,
      (horn (n + 2) 0).ι ≫ l = a ∧ l ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap f (𝟙 Y) = b := by
  let t := b ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinIntervalProjection X' Y
  have ht : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.pullCut (stdSimplex.objEquiv (SSet.yonedaEquiv t)).toOrderHom 1 = 1 := by
    rw [SSet.yonedaEquiv_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinIntervalProjection_app_cut]
    exact hb
  have hat : (horn (n + 2) 0).ι ≫ t = a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinIntervalProjection X Y := by
    change ((horn (n + 2) 0).ι ≫ b) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinIntervalProjection X' Y = _
    rw [hsq, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinIntervalProjection_naturality]
  let v := a.app (Opposite.op ⦋n + 1⦌)
    (horn.face (0 : Fin (n + 3)) (Fin.last (n + 2)) (by simp))
  have hv : v.1.val = 1 := by
    change (a.app _ (horn.face _ _ _)).1.val = 1
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join_horn_face_cut n 0 a t hat, ht]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.Join.pullCut_delta_one_of_ne_zero n _ (by simp)
  let x : X _⦋0⦌ := cast (congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augObj X) hv) v.2.1
  have hface : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap f (𝟙 Y)).app (Opposite.op ⦋n + 1⦌) v =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.simplexMap X' Y (SimplexCategory.δ (Fin.last (n + 2))).toOrderHom
        (SSet.yonedaEquiv b) := by
    have he := congrArg (fun q ↦ horn.ι (0 : Fin (n + 3)) (Fin.last (n + 2)) (by simp) ≫ q) hsq
    simp only [← Category.assoc, horn.ι_ι] at he
    have hh := congrArg SSet.yonedaEquiv he
    rw [stdSimplex.yonedaEquiv_δ_comp] at hh
    rw [SSet.yonedaEquiv_comp, SSet.yonedaEquiv_comp, horn.yonedaEquiv_ι] at hh
    exact hh.symm
  have hx : HEq (f.app (Opposite.op ⦋0⦌) x) (SSet.yonedaEquiv b).2.1 := by
    have he := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augHom_cast f hv v.2.1
    have hleft : HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augHom f v.1.val v.2.1)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.simplexMap X' Y (SimplexCategory.δ (Fin.last (n + 2))).toOrderHom
          (SSet.yonedaEquiv b)).2.1 := by
      change HEq ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap f (𝟙 Y)).app (Opposite.op ⦋n + 1⦌) v).2.1 _
      rw [hface]
    exact (heq_of_eq he.symm).trans ((cast_heq _ _).trans
      (hleft.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.Join.simplexMap_delta_last_left_heq _ (by omega))))
  obtain ⟨s, hs, hsx, hsb⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.Join.Simplex.exists_preimage_cut_one f _ hb x hx
  let l : (Δ[n + 2] : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join X Y := SSet.yonedaEquiv.symm s
  have hl : l ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap f (𝟙 Y) = b := by
    apply SSet.yonedaEquiv.injective
    simpa only [SSet.yonedaEquiv_comp, l, Equiv.apply_symm_apply] using hsb
  have hlt : l ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinIntervalProjection X Y = t := by
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinIntervalProjection_naturality f (𝟙 Y), ← Category.assoc, hl]
  refine ⟨l, ?_, hl⟩
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.join_initialHorn_hom_ext_of_initial_vertex_joinMap n f
    ((horn (n + 2) 0).ι ≫ l) a t
  · simp only [Category.assoc, hlt]
  · exact hat
  · exact ht
  · let q := horn.ι (0 : Fin (n + 3)) (Fin.last (n + 2)) (by simp)
    let α := SimplexCategory.const ⦋0⦌ ⦋n + 1⦌ 0
    change (stdSimplex.map α ≫ q) ≫ ((horn (n + 2) 0).ι ≫ l) =
      (stdSimplex.map α ≫ q) ≫ a
    have hq : q ≫ (horn (n + 2) 0).ι = stdSimplex.δ (Fin.last (n + 2)) := horn.ι_ι _ _ _
    have hm : ((horn (n + 2) 0).ι ≫ l) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap f (𝟙 Y) =
        a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap f (𝟙 Y) := by rw [Category.assoc, hl, hsq]
    have him := congrArg (fun z ↦ (stdSimplex.map α ≫ q) ≫ z) hm
    change stdSimplex.map α ≫ ((q ≫ (horn (n + 2) 0).ι) ≫ l) =
      stdSimplex.map α ≫ (q ≫ a)
    rw [hq]
    apply SSet.yonedaEquiv.injective
    rw [← SSet.yonedaEquiv_naturality, ← SSet.yonedaEquiv_naturality]
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.Join.Simplex.ext_of_joinMap_right_id f
    · rw [stdSimplex.yonedaEquiv_δ_comp, Equiv.apply_symm_apply,
        SSet.yonedaEquiv_comp, show SSet.yonedaEquiv q =
          horn.face (0 : Fin (n + 3)) (Fin.last (n + 2)) (by simp) from horn.yonedaEquiv_ι _ _ _]
      change HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.simplexMap X Y α.toOrderHom
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.simplexMap X Y (SimplexCategory.δ (Fin.last (n + 2))).toOrderHom s)).2.1
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.simplexMap X Y α.toOrderHom v).2.1
      have hc : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.simplexMap X Y
          (SimplexCategory.δ (Fin.last (n + 2))).toOrderHom s).1.val = 1 := by
        change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.pullCut (SimplexCategory.δ (Fin.last (n + 2))).toOrderHom s.1.val = 1
        rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.Join.pullCut_delta_last, hs]
        omega
      exact (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.Join.simplexMap_initial_left_heq _ hc).trans
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.Join.simplexMap_delta_last_left_heq s (by omega)).trans
          (hsx.trans ((cast_heq _ _).trans (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.Join.simplexMap_initial_left_heq v hv).symm)))
    · rw [SSet.yonedaEquiv_naturality, SSet.yonedaEquiv_naturality]
      change SSet.yonedaEquiv ((stdSimplex.map α ≫ (stdSimplex.δ (Fin.last (n + 2)) ≫ l)) ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap f (𝟙 Y)) =
        SSet.yonedaEquiv ((stdSimplex.map α ≫ (q ≫ a)) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap f (𝟙 Y))
      apply congrArg SSet.yonedaEquiv
      simpa only [← hq, Category.assoc] using him
  · rw [Category.assoc, hl, hsq]

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport
