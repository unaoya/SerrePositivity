module

public import SerrePositivity.InfinityCategories.Core.JoinComparisonFunctors
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal

/-!
概要：初期対象を因子に持つ fat join 比較。
方針：通常の join の随伴と、初期対象の直積の二段の pushout を計算する。
規約：空の因子を任意の初期対象で表す。
使われ方：Kerodon Lemma 4.6.2.10 のセル分解の初期条件。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：左因子が初期対象なら通常の join の右包含は同型。
方針：under 圏への join の左随伴が初期対象を保つことを使う。
規約：右因子 K は任意。
使われ方：Kerodon §4.6.2 の空の join の比較。 -/
lemma isIso_joinInr_of_isInitial (A : SSet.{u}) (hA : IsInitial A) (K : SSet.{u}) :
    IsIso (joinInr A K) := by
  have h := hA.isInitialObj (joinLeftUnderFunctor K)
  let m : Under.mk (𝟙 K) ⟶ (joinLeftUnderFunctor K).obj A :=
    Under.homMk (joinInr A K) (by change 𝟙 K ≫ joinInr A K = joinInr A K; rw [Category.id_comp])
  have : IsIso m := isIso_of_isInitial (Under.mkIdInitial (X := K)) h m
  exact (Under.forget K).map_isIso m

/-- 概要：右因子が初期対象なら通常の join の左包含は同型。
方針：under 圏への右変数の join の左随伴を使う。
規約：左因子 K は任意。
使われ方：Kerodon §4.6.2 の空の join の比較。 -/
lemma isIso_joinInl_of_isInitial (K A : SSet.{u}) (hA : IsInitial A) :
    IsIso (joinInl K A) := by
  have h := hA.isInitialObj (joinRightUnderFunctor K)
  let m : Under.mk (𝟙 K) ⟶ (joinRightUnderFunctor K).obj A :=
    Under.homMk (joinInl K A) (by change 𝟙 K ≫ joinInl K A = joinInl K A; rw [Category.id_comp])
  have : IsIso m := isIso_of_isInitial (Under.mkIdInitial (X := K)) h m
  exact (Under.forget K).map_isIso m

/-- 概要：左因子が初期対象なら fat join の右包含は同型。
方針：両端の円柱と左因子が初期対象であることから二つの pushout を計算する。
規約：右因子 K は任意。
使われ方：Kerodon §4.6.2 の空の fat join の比較。 -/
lemma isIso_fatJoinInr_of_isInitial (A : SSet.{u}) (hA : IsInitial A) (K : SSet.{u}) :
    IsIso (fatJoinInr A K) := by
  have hAK := hA.isInitialObj (tensorRight K)
  have hC := (hA.isInitialObj (tensorRight (Δ[1] : SSet.{u}))).isInitialObj (tensorRight K)
  have : IsIso (fst A K) := isIso_of_isInitial hAK hA _
  have : IsIso (pushout.inl (SSet.ι₀ (X := A) ▷ K) (fst A K)) :=
    (IsPushout.of_hasPushout _ _).isIso_inl_of_isIso
  have : IsIso (SSet.ι₁ (X := A) ▷ K) := isIso_of_isInitial hAK hC _
  have : IsIso (fatJoinStageEnd A K) := by unfold fatJoinStageEnd; infer_instance
  exact (IsPushout.of_hasPushout (fatJoinStageEnd A K) (snd A K)).isIso_inr_of_isIso

/-- 概要：右因子が初期対象なら fat join の左包含は同型。
方針：最初の円柱の零端と第二射影が初期対象間の同型であることを使う。
規約：左因子 K は任意。
使われ方：Kerodon §4.6.2 の空の fat join の比較。 -/
lemma isIso_fatJoinInl_of_isInitial (K A : SSet.{u}) (hA : IsInitial A) :
    IsIso (fatJoinInl K A) := by
  have hKA := hA.isInitialObj (tensorLeft K)
  have hC := hA.isInitialObj (tensorLeft (K ⊗ (Δ[1] : SSet.{u})))
  have : IsIso (SSet.ι₀ (X := K) ▷ A) := isIso_of_isInitial hKA hC _
  have : IsIso (pushout.inr (SSet.ι₀ (X := K) ▷ A) (fst K A)) :=
    (IsPushout.of_hasPushout _ _).isIso_inr_of_isIso
  have : IsIso (snd K A) := isIso_of_isInitial hKA hA _
  have : IsIso (pushout.inl (fatJoinStageEnd K A) (snd K A)) :=
    (IsPushout.of_hasPushout _ _).isIso_inl_of_isIso
  unfold fatJoinInl
  infer_instance

/-- 概要：左因子が初期対象なら fat join 比較は前合成の同値条件を満たす。
方針：左右の右包含が同型であることと比較の制限の等式を使う。
規約：右因子 K は任意。
使われ方：Kerodon Lemma 4.6.2.10 の左因子の帰納法の初期条件。 -/
lemma isPrecompositionEquivalence_fatJoinComparison_initial_left
    (A : SSet.{u}) (hA : IsInitial A) (K : SSet.{u}) :
    IsPrecompositionEquivalence (fatJoinComparison A K) := by
  have := isIso_fatJoinInr_of_isInitial A hA K
  have := isIso_joinInr_of_isInitial A hA K
  apply (isPrecompositionEquivalence_of_iso (asIso (fatJoinInr A K))).cancel_left
  change IsPrecompositionEquivalence (fatJoinInr A K ≫ fatJoinComparison A K)
  rw [fatJoinInr_comparison]
  exact isPrecompositionEquivalence_of_iso (asIso (joinInr A K))

/-- 概要：右因子が初期対象なら fat join 比較は前合成の同値条件を満たす。
方針：左右の左包含が同型であることと比較の制限の等式を使う。
規約：左因子 K は任意。
使われ方：Kerodon Lemma 4.6.2.10 の右因子の帰納法の初期条件。 -/
lemma isPrecompositionEquivalence_fatJoinComparison_initial_right
    (K A : SSet.{u}) (hA : IsInitial A) :
    IsPrecompositionEquivalence (fatJoinComparison K A) := by
  have := isIso_fatJoinInl_of_isInitial K A hA
  have := isIso_joinInl_of_isInitial K A hA
  apply (isPrecompositionEquivalence_of_iso (asIso (fatJoinInl K A))).cancel_left
  change IsPrecompositionEquivalence (fatJoinInl K A ≫ fatJoinComparison K A)
  rw [fatJoinInl_comparison]
  exact isPrecompositionEquivalence_of_iso (asIso (joinInl K A))

end SerrePositivity.InfinityCategories
