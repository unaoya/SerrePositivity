module

public import SerrePositivity.AlgebraicGeometry.ProjectiveLocalizedDirectSum

/-!
概要：直和と局所化の比較を、任意の分母を持つ元の各成分で記述する。
方針：各成分への射影との可換性を局所化の普遍性で示す。
規約：局所化する環と、その上の加群について余分な有限性を仮定しない。
使われ方：Rees 加群の各 Proj 次数と、各 IⁿM の斉次局所化の比較。
-/

@[expose] public noncomputable section

namespace SerrePositivity.AlgebraicGeometry

open scoped DirectSum
attribute [local instance] LocalizedModule.moduleOfIsLocalization

variable {R κ : Type*} [CommRing R] [DecidableEq κ]
variable (S : Submonoid R) (M : κ → Type*) [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]

/-- 局所化と直和の比較は、各成分への射影に自然。 -/
theorem projectiveLocalizationToDirectSum_component (i : κ) :
    (DirectSum.component R κ (fun i ↦ LocalizedModule S (M i)) i).comp
        (projectiveLocalizationToDirectSum S M) =
      IsLocalizedModule.map S (LocalizedModule.mkLinearMap S (⨁ i, M i))
        (LocalizedModule.mkLinearMap S (M i)) (DirectSum.component R κ M i) := by
  apply IsLocalizedModule.linearMap_ext S (LocalizedModule.mkLinearMap S (⨁ i, M i))
    (LocalizedModule.mkLinearMap S (M i))
  apply LinearMap.ext
  intro x
  simp only [LinearMap.comp_apply, projectiveLocalizationToDirectSum,
    IsLocalizedModule.map_apply, LinearMap.id_apply]
  rfl

/-- 任意の分母を持つ元の第 i 成分は、分子の第 i 成分を同じ分母で割ったもの。 -/
theorem projectiveLocalizedDirectSumLinearEquiv_mk_component
    (x : ⨁ i, M i) (s : S) (i : κ) :
    (projectiveLocalizedDirectSumLinearEquiv S M (LocalizedModule.mk x s)) i =
      LocalizedModule.mk (x i) s := by
  have h := DFunLike.congr_fun (projectiveLocalizationToDirectSum_component S M i)
    (LocalizedModule.mk x s)
  change (projectiveLocalizedDirectSumLinearEquiv S M (LocalizedModule.mk x s)) i = _ at h
  rw [IsLocalizedModule.map_LocalizedModules] at h
  exact h

section Congr

variable {A N : Type*} [AddCommGroup A] [AddCommGroup N] [Module R A] [Module R N]

/-- 係数加群の線形同値を局所化へ移す。 -/
def projectiveLocalizedModuleCongr (e : A ≃ₗ[R] N) :
    LocalizedModule S A ≃ₗ[R] LocalizedModule S N :=
  LinearEquiv.ofLinearMap
    (IsLocalizedModule.map S (LocalizedModule.mkLinearMap S A)
      (LocalizedModule.mkLinearMap S N) e.toLinearMap)
    (IsLocalizedModule.map S (LocalizedModule.mkLinearMap S N)
      (LocalizedModule.mkLinearMap S A) e.symm.toLinearMap) (by
        apply IsLocalizedModule.linearMap_ext S (LocalizedModule.mkLinearMap S N)
          (LocalizedModule.mkLinearMap S N)
        apply LinearMap.ext
        intro x
        simp only [LinearMap.comp_apply, IsLocalizedModule.map_apply,
          LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply, LinearMap.id_apply]) (by
        apply IsLocalizedModule.linearMap_ext S (LocalizedModule.mkLinearMap S A)
          (LocalizedModule.mkLinearMap S A)
        apply LinearMap.ext
        intro x
        simp only [LinearMap.comp_apply, IsLocalizedModule.map_apply,
          LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply, LinearMap.id_apply])

/-- 加群の局所化の同値は分子に元の同値を適用する。 -/
theorem projectiveLocalizedModuleCongr_mk (e : A ≃ₗ[R] N) (x : A) (s : S) :
    projectiveLocalizedModuleCongr S e (LocalizedModule.mk x s) =
      LocalizedModule.mk (e x) s :=
  IsLocalizedModule.map_LocalizedModules S e.toLinearMap x s

end Congr

end SerrePositivity.AlgebraicGeometry
