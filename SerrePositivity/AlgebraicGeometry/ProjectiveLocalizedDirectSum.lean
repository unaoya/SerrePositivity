module

public import Mathlib.Algebra.Module.LocalizedModule.IsLocalization
public import Mathlib.Algebra.DirectSum.Module

/-!
概要：加群の局所化と外部直和の交換を、係数の自然な線形同値として与える。
方針：各成分の包含を局所化し、普遍性と直和の外延性で互いに逆と示す。
規約：任意の添字集合と分母部分モノイドを許す。
使われ方：Rees 次数ごとの標準開の切断と、その直和の Čech 計算の比較。
-/

@[expose] public noncomputable section

namespace SerrePositivity.AlgebraicGeometry

open scoped DirectSum

attribute [local instance] LocalizedModule.moduleOfIsLocalization

variable {R κ : Type*} [CommRing R] [DecidableEq κ]
variable (S : Submonoid R) (M : κ → Type*) [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]

instance projectiveSumLocalized_isLocalized :
    IsLocalizedModule S
      (LinearMap.id : (⨁ i, LocalizedModule S (M i)) →ₗ[R] ⨁ i, LocalizedModule S (M i)) :=
  isLocalizedModule_id (S := S) _ (Localization S)

/-- 直和を局所化してから、各成分の局所化の直和へ送る。 -/
def projectiveLocalizationToDirectSum :
    LocalizedModule S (⨁ i, M i) →ₗ[R] ⨁ i, LocalizedModule S (M i) :=
  IsLocalizedModule.map S (LocalizedModule.mkLinearMap S (⨁ i, M i)) LinearMap.id
    (DirectSum.lmap (fun i ↦ LocalizedModule.mkLinearMap S (M i)))

/-- 各成分の包含を局所化し、局所化の直和から直和の局所化へ送る。 -/
def projectiveDirectSumToLocalization :
    (⨁ i, LocalizedModule S (M i)) →ₗ[R] LocalizedModule S (⨁ i, M i) :=
  DirectSum.toModule R κ _ (fun i ↦
    IsLocalizedModule.map S (LocalizedModule.mkLinearMap S (M i))
      (LocalizedModule.mkLinearMap S (⨁ i, M i)) (DirectSum.lof R κ M i))

theorem projectiveDirectSumLocalization_left :
    (projectiveDirectSumToLocalization S M).comp (projectiveLocalizationToDirectSum S M) =
      LinearMap.id := by
  apply IsLocalizedModule.linearMap_ext S (LocalizedModule.mkLinearMap S (⨁ i, M i))
    (LocalizedModule.mkLinearMap S (⨁ i, M i))
  apply DirectSum.linearMap_ext
  intro i
  apply LinearMap.ext
  intro m
  simp only [LinearMap.comp_apply, projectiveLocalizationToDirectSum,
    IsLocalizedModule.map_apply, LinearMap.id_apply, DirectSum.lmap_lof,
    projectiveDirectSumToLocalization, DirectSum.toModule_lof]

theorem projectiveDirectSumLocalization_right :
    (projectiveLocalizationToDirectSum S M).comp (projectiveDirectSumToLocalization S M) =
      LinearMap.id := by
  apply DirectSum.linearMap_ext
  intro i
  apply IsLocalizedModule.linearMap_ext S (LocalizedModule.mkLinearMap S (M i))
    (LinearMap.id : (⨁ i, LocalizedModule S (M i)) →ₗ[R] _)
  apply LinearMap.ext
  intro m
  simp only [LinearMap.comp_apply, projectiveDirectSumToLocalization,
    DirectSum.toModule_lof, IsLocalizedModule.map_apply,
    projectiveLocalizationToDirectSum, DirectSum.lmap_lof, LinearMap.id_apply]

/-- 局所化は外部直和と交換する。 -/
def projectiveLocalizedDirectSumLinearEquiv :
    LocalizedModule S (⨁ i, M i) ≃ₗ[R] ⨁ i, LocalizedModule S (M i) :=
  LinearEquiv.ofLinearMap (projectiveLocalizationToDirectSum S M)
    (projectiveDirectSumToLocalization S M)
    (projectiveDirectSumLocalization_right S M) (projectiveDirectSumLocalization_left S M)

/-- 比較は、分母一の各成分を同じ成分へ送る。 -/
@[simp]
theorem projectiveLocalizedDirectSumLinearEquiv_mk_lof (i : κ) (m : M i) :
    projectiveLocalizedDirectSumLinearEquiv S M
      (LocalizedModule.mkLinearMap S (⨁ i, M i) (DirectSum.lof R κ M i m)) =
        DirectSum.lof R κ (fun i ↦ LocalizedModule S (M i)) i
          (LocalizedModule.mkLinearMap S (M i) m) := by
  change projectiveLocalizationToDirectSum S M
    (LocalizedModule.mkLinearMap S (⨁ i, M i) (DirectSum.lof R κ M i m)) = _
  simp only [projectiveLocalizationToDirectSum, IsLocalizedModule.map_apply,
    LinearMap.id_apply, DirectSum.lmap_lof]

/-- 直和と局所化の比較は、係数の線形写像に自然。 -/
theorem projectiveLocalizationToDirectSum_naturality
    (N : κ → Type*) [∀ i, AddCommGroup (N i)] [∀ i, Module R (N i)]
    (f : ∀ i, M i →ₗ[R] N i) :
    (projectiveLocalizationToDirectSum S N).comp
        (IsLocalizedModule.map S (LocalizedModule.mkLinearMap S (⨁ i, M i))
          (LocalizedModule.mkLinearMap S (⨁ i, N i)) (DirectSum.lmap f)) =
      (DirectSum.lmap (fun i ↦ IsLocalizedModule.map S
        (LocalizedModule.mkLinearMap S (M i)) (LocalizedModule.mkLinearMap S (N i)) (f i))).comp
          (projectiveLocalizationToDirectSum S M) := by
  apply IsLocalizedModule.linearMap_ext S (LocalizedModule.mkLinearMap S (⨁ i, M i))
    (LinearMap.id : (⨁ i, LocalizedModule S (N i)) →ₗ[R] _)
  apply DirectSum.linearMap_ext
  intro i
  apply LinearMap.ext
  intro m
  simp only [LinearMap.comp_apply, IsLocalizedModule.map_apply,
    projectiveLocalizationToDirectSum, LinearMap.id_apply, DirectSum.lmap_lof]

end SerrePositivity.AlgebraicGeometry
