module

public import SerrePositivity.InfinityCategories.Core.IntervalEndpointPullback
public import SerrePositivity.InfinityCategories.Core.PushoutMonoCube
public import Mathlib.CategoryTheory.Adhesive.Basic

/-!
概要：fat join の左因子の単射の保存。
方針：零端の pushout の自然性を van Kampen 性で調べ、一端の pushout の単射判定を使う。
規約：右因子は任意、quasicategory 性は不要。
使われ方：Kerodon Lemma 4.6.2.10 の左因子のセル分解。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：fat join の最初の pushout に左因子の射を作用させる。
方針：円柱と零端の写像を貼り合わせる。
規約：固定する右因子は K。
使われ方：Kerodon Lemma 4.6.2.10 の自然性の正方形。 -/
noncomputable def fatJoinStageMapLeft {A B : SSet.{u}} (f : A ⟶ B) (K : SSet.{u}) :
    fatJoinStage A K ⟶ fatJoinStage B K :=
  pushout.desc (fatJoinCylinderMap f (𝟙 K) ≫ pushout.inl _ _) (f ≫ pushout.inr _ _)
    (by rw [← Category.assoc, fatJoinCylinderMap_zero, Category.assoc,
      pushout.condition, ← Category.assoc, tensorHom_fst, Category.assoc])

/-- 概要：最初の pushout の誘導射の円柱上の制限。
方針：pushout の desc の計算。
規約：左包含は円柱からの射。
使われ方：Kerodon Lemma 4.6.2.10 の自然性。 -/
lemma fatJoinStageMapLeft_inl {A B : SSet.{u}} (f : A ⟶ B) (K : SSet.{u}) :
    pushout.inl (SSet.ι₀ (X := A) ▷ K) (fst A K) ≫ fatJoinStageMapLeft f K =
      fatJoinCylinderMap f (𝟙 K) ≫ pushout.inl _ _ := pushout.inl_desc _ _ _

/-- 概要：最初の pushout の誘導射の零端上の制限。
方針：pushout の desc の計算。
規約：右包含は左因子からの射。
使われ方：Kerodon Lemma 4.6.2.10 の自然性。 -/
lemma fatJoinStageMapLeft_inr {A B : SSet.{u}} (f : A ⟶ B) (K : SSet.{u}) :
    pushout.inr (SSet.ι₀ (X := A) ▷ K) (fst A K) ≫ fatJoinStageMapLeft f K =
      f ≫ pushout.inr _ _ := pushout.inr_desc _ _ _

/-- 概要：左因子の単射は fat join の最初の pushout で単射を誘導する。
方針：零端の円柱側の正方形が pullback であることを使う。
規約：右因子 K は任意。
使われ方：Kerodon Lemma 4.6.2.10 のセルの包含。 -/
instance fatJoinStageMapLeft_mono {A B : SSet.{u}} (f : A ⟶ B) [Mono f] (K : SSet.{u}) :
    Mono (fatJoinStageMapLeft f K) := by
  have : Mono (SSet.ι₀ (X := B) ▷ K) := (tensorRight K).map_mono _
  have : Mono (f ▷ (Δ[1] : SSet.{u})) := (tensorRight _).map_mono f
  have : Mono (fatJoinCylinderMap f (𝟙 K)) := by
    change Mono ((f ▷ (Δ[1] : SSet.{u})) ▷ K)
    exact (tensorRight K).map_mono _
  exact mono_of_pushout_cube (IsPushout.of_hasPushout _ _) (IsPushout.of_hasPushout _ _)
    (f ▷ K) (fatJoinCylinderMap f (𝟙 K)) f (fatJoinStageMapLeft f K)
    (isPullback_whiskerRight (isPullback_ι₀_naturality f) K)
    (whiskerRight_fst f K).symm (fatJoinStageMapLeft_inl f K) (fatJoinStageMapLeft_inr f K)

/-- 概要：最初の pushout の円柱の包含の自然性の正方形は pullback。
方針：零端と射影の自然性の pullback を van Kampen 性で移す。
規約：左因子の射 f に単射性は不要。
使われ方：Kerodon Lemma 4.6.2.10 の残った端点の逆像。 -/
lemma fatJoinStageMapLeft_inl_isPullback {A B : SSet.{u}} (f : A ⟶ B) (K : SSet.{u}) :
    IsPullback (pushout.inl (SSet.ι₀ (X := A) ▷ K) (fst A K))
      (fatJoinCylinderMap f (𝟙 K)) (fatJoinStageMapLeft f K)
      (pushout.inl (SSet.ι₀ (X := B) ▷ K) (fst B K)) := by
  have : Mono (SSet.ι₀ (X := B) ▷ K) := (tensorRight K).map_mono _
  have h := IsPushout.of_hasPushout (SSet.ι₀ (X := A) ▷ K) (fst A K)
  have h' := IsPushout.of_hasPushout (SSet.ι₀ (X := B) ▷ K) (fst B K)
  exact ((Adhesive.van_kampen h') _ _ _ _ (f ▷ K)
    (fatJoinCylinderMap f (𝟙 K)) f (fatJoinStageMapLeft f K)
    (isPullback_whiskerRight (isPullback_ι₀_naturality f) K)
    (isPullback_fst_whiskerRight f K)
    ⟨fatJoinStageMapLeft_inl f K⟩ ⟨fatJoinStageMapLeft_inr f K⟩ h.toCommSq).mp h |>.1

/-- 概要：残った一端の自然性の正方形は pullback。
方針：一端の円柱の pullback と最初の pushout の円柱の pullback を貼り合わせる。
規約：左因子の射 f は任意。
使われ方：Kerodon Lemma 4.6.2.10 の第二の pushout の比較。 -/
lemma fatJoinStageEnd_left_isPullback {A B : SSet.{u}} (f : A ⟶ B) (K : SSet.{u}) :
    IsPullback (fatJoinStageEnd A K) (f ▷ K) (fatJoinStageMapLeft f K)
      (fatJoinStageEnd B K) :=
  (isPullback_whiskerRight (isPullback_ι₁_naturality f) K).paste_horiz
    (fatJoinStageMapLeft_inl_isPullback f K)

/-- 概要：fat join の最初の pushout に残った一端は単射。
方針：零端と一端が交わらないことから pushout 後の単射性を得る。
規約：両因子は任意。
使われ方：Kerodon Lemma 4.6.2.10 の第二の貼り合わせ。 -/
instance fatJoinStageEnd_mono (A K : SSet.{u}) : Mono (fatJoinStageEnd A K) := by
  have : Mono (SSet.ι₁ (X := A) ▷ K) := (tensorRight K).map_mono _
  apply mono_pushout_inl_comp_of_disjoint (IsPushout.of_hasPushout _ _)
  intro n a b he
  obtain ⟨⟨n⟩⟩ := n
  have hh := congrArg (fun z : ((A ⊗ (Δ[1] : SSet.{u})) ⊗ K) _⦋n⦌ ↦ z.1.2 0) he
  exact (show (0 : Fin 2) ≠ 1 by decide) hh

/-- 概要：左因子の単射は fat join の単射を誘導する。
方針：最初の pushout の単射と残った端点の逆像の一致を第二の pushout に適用する。
規約：右因子 K は任意。
使われ方：Kerodon Lemma 4.6.2.10 の左因子のセル分解。 -/
instance fatJoinMap_left_mono {A B : SSet.{u}} (f : A ⟶ B) [Mono f] (K : SSet.{u}) :
    Mono (fatJoinMap f (𝟙 K)) := by
  apply mono_of_pushout_cube (IsPushout.of_hasPushout _ _) (IsPushout.of_hasPushout _ _)
    (f ▷ K) (fatJoinStageMapLeft f K) (𝟙 K) (fatJoinMap f (𝟙 K))
    (fatJoinStageEnd_left_isPullback f K)
  · simpa using (tensorHom_snd f (𝟙 K)).symm
  · apply pushout.hom_ext
    · simpa only [fatJoinCylinder, Category.assoc, reassoc_of% fatJoinStageMapLeft_inl] using
        fatJoinCylinder_map f (𝟙 K)
    · simpa only [fatJoinInl, Category.assoc, reassoc_of% fatJoinStageMapLeft_inr] using
        fatJoinInl_map f (𝟙 K)
  · exact fatJoinInr_map f (𝟙 K)

end SerrePositivity.InfinityCategories
