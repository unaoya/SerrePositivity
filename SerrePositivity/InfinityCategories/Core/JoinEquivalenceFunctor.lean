module

public import SerrePositivity.InfinityCategories.Core.FatJoinGeneralComparison
public import SerrePositivity.InfinityCategories.Core.PrecompositionPushoutGluing
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：join と fat join による前合成の同値条件の保存。
方針：fat join の二段の pushout を比較し、通常の join へ一般比較を通じて移す。
規約：同値条件を満たす射の単射性は要求しない。
使われ方：Kerodon Corollary 4.6.2.9、Lemma 4.6.4.25 の相対的な円柱。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：左因子の前合成の同値条件は fat join の第一の pushout で保存される。
方針：零端の二つの pushout の三頂点の同値条件を貼る。
規約：元の射 f は単射でなくてよい。
使われ方：Kerodon Corollary 4.6.2.9 の第一段階。 -/
lemma IsPrecompositionEquivalence.fatJoinStageMapLeft_equivalence {A B : SSet.{u}} {f : A ⟶ B}
    (hf : IsPrecompositionEquivalence f) (K : SSet.{u}) :
    IsPrecompositionEquivalence (fatJoinStageMapLeft f K) := by
  have : Mono (SSet.ι₀ (X := A) ▷ K) := (tensorRight K).map_mono _
  have : Mono (SSet.ι₀ (X := B) ▷ K) := (tensorRight K).map_mono _
  exact isPrecompositionEquivalence_of_pushout_gluing
    (IsPushout.of_hasPushout _ _) (IsPushout.of_hasPushout _ _)
    (f ▷ K) (fatJoinCylinderMap f (𝟙 K)) f (fatJoinStageMapLeft f K)
    (fatJoinCylinderMap_zero f (𝟙 K)) (whiskerRight_fst f K).symm
    (fatJoinStageMapLeft_inl f K) (fatJoinStageMapLeft_inr f K)
    (hf.whiskerRight K) ((hf.whiskerRight (Δ[1] : SSet.{u})).whiskerRight K) hf

/-- 概要：右因子の前合成の同値条件は fat join の第一の pushout で保存される。
方針：円柱と零端の自然性の正方形の比較を貼る。
規約：元の射 f は単射でなくてよい。
使われ方：Kerodon Corollary 4.6.2.9 の第一段階。 -/
lemma IsPrecompositionEquivalence.fatJoinStageMapRight_equivalence {A B : SSet.{u}} {f : A ⟶ B}
    (hf : IsPrecompositionEquivalence f) (K : SSet.{u}) :
    IsPrecompositionEquivalence (fatJoinStageMapRight K f) := by
  have : Mono (SSet.ι₀ (X := K) ▷ A) := (tensorRight A).map_mono _
  have : Mono (SSet.ι₀ (X := K) ▷ B) := (tensorRight B).map_mono _
  exact isPrecompositionEquivalence_of_pushout_gluing
    (IsPushout.of_hasPushout _ _) (IsPushout.of_hasPushout _ _)
    (K ◁ f) (fatJoinCylinderMap (𝟙 K) f) (𝟙 K) (fatJoinStageMapRight K f)
    (fatJoinCylinderMap_zero (𝟙 K) f) (by simpa using (tensorHom_fst (𝟙 K) f).symm)
    (fatJoinStageMapRight_inl K f) ((fatJoinStageRightInrNat K).naturality f).symm
    (hf.whiskerLeft K) (hf.whiskerLeft (K ⊗ (Δ[1] : SSet.{u})))
    (isPrecompositionEquivalence_id K)

/-- 概要：fat join の左変数は前合成の同値条件を保つ。
方針：第一の pushout の比較と残った一端の比較を貼る。
規約：右因子 K は任意、射 f の単射性は不要。
使われ方：Kerodon Corollary 4.6.2.9 の fat join 版。 -/
lemma IsPrecompositionEquivalence.fatJoinMap_left {A B : SSet.{u}} {f : A ⟶ B}
    (hf : IsPrecompositionEquivalence f) (K : SSet.{u}) :
    IsPrecompositionEquivalence (fatJoinMap f (𝟙 K)) := by
  exact isPrecompositionEquivalence_of_pushout_gluing
    (IsPushout.of_hasPushout _ _) (IsPushout.of_hasPushout _ _)
    (f ▷ K) (fatJoinStageMapLeft f K) (𝟙 K) (fatJoinMap f (𝟙 K))
    (fatJoinStageEnd_left_isPullback f K).w (by simpa using (tensorHom_snd f (𝟙 K)).symm)
    ((fatJoinLeftInlNat K).naturality f).symm (fatJoinInr_map f (𝟙 K))
    (hf.whiskerRight K) (hf.fatJoinStageMapLeft_equivalence K) (isPrecompositionEquivalence_id K)

/-- 概要：fat join の右変数は前合成の同値条件を保つ。
方針：第一の pushout の比較と残った一端の比較を貼る。
規約：左因子 K は任意、射 f の単射性は不要。
使われ方：Kerodon Corollary 4.6.2.9 の fat join 版。 -/
lemma IsPrecompositionEquivalence.fatJoinMap_right {A B : SSet.{u}} {f : A ⟶ B}
    (hf : IsPrecompositionEquivalence f) (K : SSet.{u}) :
    IsPrecompositionEquivalence (fatJoinMap (𝟙 K) f) := by
  exact isPrecompositionEquivalence_of_pushout_gluing
    (IsPushout.of_hasPushout _ _) (IsPushout.of_hasPushout _ _)
    (K ◁ f) (fatJoinStageMapRight K f) f (fatJoinMap (𝟙 K) f)
    (fatJoinStageEnd_right_isPullback K f).w (by simpa using (tensorHom_snd (𝟙 K) f).symm)
    ((fatJoinRightInlNat K).naturality f).symm (fatJoinInr_map (𝟙 K) f)
    (hf.whiskerLeft K) (hf.fatJoinStageMapRight_equivalence K) hf

/-- 概要：通常の join の左変数は前合成の同値条件を保つ。
方針：fat join での保存を一般の比較射と自然性で移す。
規約：右因子 K は任意、射 f の単射性は不要。
使われ方：Kerodon Corollary 4.6.2.9。 -/
@[kerodon 01HW]
lemma IsPrecompositionEquivalence.joinMap_left {A B : SSet.{u}} {f : A ⟶ B}
    (hf : IsPrecompositionEquivalence f) (K : SSet.{u}) :
    IsPrecompositionEquivalence (joinMap f (𝟙 K)) := by
  have h := (hf.fatJoinMap_left K).comp (isPrecompositionEquivalence_fatJoinComparison B K)
  rw [fatJoinComparison_naturality] at h
  exact (isPrecompositionEquivalence_fatJoinComparison A K).cancel_left h

/-- 概要：通常の join の右変数は前合成の同値条件を保つ。
方針：fat join での保存を一般の比較射と自然性で移す。
規約：左因子 K は任意、射 f の単射性は不要。
使われ方：Kerodon Corollary 4.6.2.9。 -/
@[kerodon 01HW]
lemma IsPrecompositionEquivalence.joinMap_right {A B : SSet.{u}} {f : A ⟶ B}
    (hf : IsPrecompositionEquivalence f) (K : SSet.{u}) :
    IsPrecompositionEquivalence (joinMap (𝟙 K) f) := by
  have h := (hf.fatJoinMap_right K).comp (isPrecompositionEquivalence_fatJoinComparison K B)
  rw [fatJoinComparison_naturality] at h
  exact (isPrecompositionEquivalence_fatJoinComparison K A).cancel_left h

end SerrePositivity.InfinityCategories
