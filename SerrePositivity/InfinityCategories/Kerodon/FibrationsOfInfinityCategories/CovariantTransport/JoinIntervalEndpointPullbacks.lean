module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.JoinIntervalProjection
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.JoinEndpointPullbacks

/-!
概要：join の区間への射の両端は元の両因子。
方針：点への joinMap の pullback を標準区間との同型で移す。
規約：全ての単体集合を扱い、充填性を要求しない。
使われ方：Kerodon Lemma 5.2.3.12（Tag 024D）、区間が定値となる内ホーンの処理。

対応節は Kerodon 5.2（Tag 019A）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport

/-- 概要：join の左包含は区間の零頂点に沿う pullback。
方針：左包含の自然性を二点の join の同型で区間へ移す。
規約：左因子から点への射は唯一の射。
使われ方：Kerodon Lemma 5.2.3.12（Tag 024D）、時間が零に定値となる場合。 -/
lemma joinIntervalProjection_inl_isPullback (X Y : SSet.{u}) :
    IsPullback (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl X Y) (stdSimplex.isTerminalObj₀.from X) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinIntervalProjection X Y)
      (SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 2))) := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.isPullback_joinInl_naturality (stdSimplex.isTerminalObj₀.from X)
    (stdSimplex.isTerminalObj₀.from Y)).of_iso
      (Iso.refl _) (Iso.refl _) (Iso.refl _) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0)
  · simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
  · simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
  · simp only [Iso.refl_hom, Category.id_comp]
    rfl
  · simp only [Iso.refl_hom, Category.id_comp]
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso_inl_vertex, SSet.yonedaEquiv_symm_zero]

/-- 概要：join の右包含は区間の一頂点に沿う pullback。
方針：右包含の自然性を二点の join の同型で区間へ移す。
規約：右因子から点への射は唯一の射。
使われ方：Kerodon Lemma 5.2.3.12（Tag 024D）、時間が一に定値となる場合。 -/
lemma joinIntervalProjection_inr_isPullback (X Y : SSet.{u}) :
    IsPullback (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr X Y) (stdSimplex.isTerminalObj₀.from Y) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinIntervalProjection X Y)
      (SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.isPullback_joinInr_naturality (stdSimplex.isTerminalObj₀.from X)
    (stdSimplex.isTerminalObj₀.from Y)).of_iso
      (Iso.refl _) (Iso.refl _) (Iso.refl _) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0)
  · simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
  · simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
  · simp only [Iso.refl_hom, Category.id_comp]
    rfl
  · simp only [Iso.refl_hom, Category.id_comp]
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso_inr_vertex, SSet.yonedaEquiv_symm_zero]
    rfl

/-- 概要：時間が零に定値である join への射は左因子を経由する。
方針：零端の pullback の普遍性を使う。
規約：始域 K の充填性は要求しない。
使われ方：Kerodon Lemma 5.2.3.12（Tag 024D）、左因子だけに入る指定単体の復元。 -/
lemma join_exists_factor_inl_of_interval_zero {K X Y : SSet.{u}} (b : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join X Y)
    (hb : b ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinIntervalProjection X Y = SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 2))) :
    ∃ c : K ⟶ X, c ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl X Y = b := by
  let hp := joinIntervalProjection_inl_isPullback X Y
  have h : b ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinIntervalProjection X Y = stdSimplex.isTerminalObj₀.from K ≫
      SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) := by rw [hb, SSet.comp_const]
  exact ⟨hp.lift b (stdSimplex.isTerminalObj₀.from K) h, hp.lift_fst _ _ _⟩

/-- 概要：時間が一に定値である join への射は右因子を経由する。
方針：一端の pullback の普遍性を使う。
規約：始域 K の充填性は要求しない。
使われ方：Kerodon Lemma 5.2.3.12（Tag 024D）、右因子だけに入る指定単体の復元。 -/
lemma join_exists_factor_inr_of_interval_one {K X Y : SSet.{u}} (b : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join X Y)
    (hb : b ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinIntervalProjection X Y = SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) :
    ∃ c : K ⟶ Y, c ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr X Y = b := by
  let hp := joinIntervalProjection_inr_isPullback X Y
  have h : b ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinIntervalProjection X Y = stdSimplex.isTerminalObj₀.from K ≫
      SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) := by rw [hb, SSet.comp_const]
  exact ⟨hp.lift b (stdSimplex.isTerminalObj₀.from K) h, hp.lift_fst _ _ _⟩

/-- 概要：join の左包含は区間の零頂点へ写る。
方針：零端の pullback の可換性を定値射の合成で簡約する。
規約：因子 X と Y は任意。
使われ方：Kerodon Lemma 5.2.3.12（Tag 024D）、片側に入る指定単体の射影。 -/
lemma joinIntervalProjection_inl (X Y : SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl X Y ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinIntervalProjection X Y =
      SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) := by
  rw [(joinIntervalProjection_inl_isPullback X Y).w, SSet.comp_const]

/-- 概要：join の右包含は区間の一頂点へ写る。
方針：一端の pullback の可換性を定値射の合成で簡約する。
規約：因子 X と Y は任意。
使われ方：Kerodon Lemma 5.2.3.12（Tag 024D）、片側に入る指定単体の射影。 -/
lemma joinIntervalProjection_inr (X Y : SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr X Y ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinIntervalProjection X Y =
      SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) := by
  rw [(joinIntervalProjection_inr_isPullback X Y).w, SSet.comp_const]

/-- 概要：切断が全頂点数である標準単体からの射は左因子を経由する。
方針：Yoneda に対応する単体を左包含から復元する。
規約：n は標準単体の次元。
使われ方：Kerodon Lemma 5.2.3.12（Tag 024D）、内ホーンの左端の分岐。 -/
lemma join_hom_exists_factor_inl_of_cut {X Y : SSet.{u}} {n : ℕ}
    (b : (Δ[n] : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join X Y) (hb : (SSet.yonedaEquiv b).1.val = n + 1) :
    ∃ c : (Δ[n] : SSet.{u}) ⟶ X, c ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl X Y = b := by
  obtain ⟨c, hc⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinSimplex_exists_inl_of_cut (SSet.yonedaEquiv b) hb
  refine ⟨SSet.yonedaEquiv.symm c, ?_⟩
  apply SSet.yonedaEquiv.injective
  rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply]
  exact hc

/-- 概要：切断が零である標準単体からの射は右因子を経由する。
方針：Yoneda に対応する単体を右包含から復元する。
規約：n は標準単体の次元。
使われ方：Kerodon Lemma 5.2.3.12（Tag 024D）、内ホーンの右端の分岐。 -/
lemma join_hom_exists_factor_inr_of_cut {X Y : SSet.{u}} {n : ℕ}
    (b : (Δ[n] : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join X Y) (hb : (SSet.yonedaEquiv b).1.val = 0) :
    ∃ c : (Δ[n] : SSet.{u}) ⟶ Y, c ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr X Y = b := by
  obtain ⟨c, hc⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinSimplex_exists_inr_of_cut (SSet.yonedaEquiv b) hb
  refine ⟨SSet.yonedaEquiv.symm c, ?_⟩
  apply SSet.yonedaEquiv.injective
  rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply]
  exact hc

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport
