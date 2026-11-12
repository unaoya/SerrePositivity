module

public import SerrePositivity.AlgebraicGeometry.ProjectiveRightTensorLocalization
public import Mathlib.RingTheory.Flat.Basic

/-!
概要：指定した分子族の斉次局所化と、右テンソル積を比較する。
方針：分数写像の像の上限を純テンソルで比較し、flat な場合は単射性を使う。
規約：局所化する環 P は固定し、テンソルの基底環 R と区別する。
使われ方：基底変更後の標準開の指定次数部分を、元の標準開のテンソル積へ戻す。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open scoped TensorProduct
variable {R P M N : Type*} [CommRing R] [CommRing P] [Algebra R P]
variable [AddCommGroup M] [Module R M] [Module P M] [IsScalarTower R P M]
variable [AddCommGroup N] [Module R N]
variable (f : P) (V : ℕ → Submodule R M)

/-- 分子族の右テンソル像を、元の基底環上の部分加群として扱う。 -/
def projectiveTensorNumerator (n : ℕ) : Submodule R (M ⊗[R] N) :=
  LinearMap.range ((V n).subtype.rTensor N)

/-- 純テンソルの斉次分数は、テンソル像の分子族に属する。 -/
theorem projectiveTensorNumerator_fraction_mem (n : ℕ) (m : V n) (b : N) :
    LocalizedModule.mk (m.val ⊗ₜ[R] b) (projDenominator f n) ∈
      projectiveGradedAway f (projectiveTensorNumerator (N := N) V) := by
  apply (le_iSup (fun k ↦ LinearMap.range
    (projectiveGradedFraction f (projectiveTensorNumerator (N := N) V) k)) n)
  exact ⟨⟨m.val ⊗ₜ[R] b, ⟨m ⊗ₜ[R] b, rfl⟩⟩,
    projectiveGradedFraction_apply _ _ _ _⟩

/-- 周囲の局所化の比較の逆は、元の指定次数部分の純テンソルを保つ。 -/
theorem projectiveGradedTensorLocalization_symm_tmul_mem
    (u : projectiveGradedAway f V) (b : N) :
    (projectiveRightTensorLocalizationEquiv (R := R) (Submonoid.powers f)).symm
        (u.val ⊗ₜ[R] b) ∈
      projectiveGradedAway f (projectiveTensorNumerator (N := N) V) := by
  let e := (projectiveRightTensorLocalizationEquiv
    (R := R) (M := M) (N := N) (Submonoid.powers f)).restrictScalars R
  let h : LocalizedModule (Submonoid.powers f) M →ₗ[R]
      LocalizedModule (Submonoid.powers f) (M ⊗[R] N) :=
    e.symm.toLinearMap.comp ((TensorProduct.mk R _ _).flip b)
  have hle : projectiveGradedAway f V ≤
      (projectiveGradedAway f (projectiveTensorNumerator (N := N) V)).comap h := by
    apply iSup_le
    intro n x hx
    obtain ⟨m, rfl⟩ := hx
    change e.symm (projectiveGradedFraction f V n m ⊗ₜ[R] b) ∈
      projectiveGradedAway f (projectiveTensorNumerator (N := N) V)
    rw [projectiveGradedFraction_apply]
    have he := projectiveRightTensorLocalizationEquiv_mk
      (R := R) (Submonoid.powers f) m.val b (projDenominator f n)
    rw [← he]
    change e.symm (e _) ∈ _
    rw [e.symm_apply_apply]
    exact projectiveTensorNumerator_fraction_mem f V n m b
  exact hle u.property

/-- 右テンソル像の指定次数部分への、元の斉次局所化からの比較写像。 -/
def projectiveGradedTensorLocalizationMap :
    (projectiveGradedAway f V) ⊗[R] N →ₗ[R]
      projectiveGradedAway f (projectiveTensorNumerator (N := N) V) := by
  let e := (projectiveRightTensorLocalizationEquiv
    (R := R) (M := M) (N := N) (Submonoid.powers f)).restrictScalars R
  let h := e.symm.toLinearMap.comp ((projectiveGradedAway f V).subtype.rTensor N)
  refine h.codRestrict _ ?_
  intro z
  induction z using TensorProduct.inductionOn with
  | tmul u b => exact projectiveGradedTensorLocalization_symm_tmul_mem f V u b
  | add x y hx hy => simpa only [map_add] using Submodule.add_mem _ hx hy

/-- 斉次局所化の比較写像の周囲での値は、通常の局所化比較の逆である。 -/
theorem projectiveGradedTensorLocalizationMap_val
    (z : (projectiveGradedAway f V) ⊗[R] N) :
    (projectiveGradedTensorLocalizationMap (N := N) f V z).val =
      (projectiveRightTensorLocalizationEquiv (R := R) (Submonoid.powers f)).symm
        (((projectiveGradedAway f V).subtype.rTensor N) z) := rfl

/-- flat な右テンソル積では、斉次局所化の比較写像は単射。 -/
theorem projectiveGradedTensorLocalizationMap_injective [Module.Flat R N] :
    Function.Injective (projectiveGradedTensorLocalizationMap (N := N) f V) := by
  intro x y h
  apply Module.Flat.rTensor_preserves_injective_linearMap
    (projectiveGradedAway f V).subtype Subtype.val_injective
  apply (projectiveRightTensorLocalizationEquiv
    (R := R) (M := M) (N := N) (Submonoid.powers f)).symm.injective
  exact congrArg Subtype.val h

/-- 純テンソルの比較写像は、元の分数の分母を保つ。 -/
theorem projectiveGradedTensorLocalizationMap_fraction (n : ℕ) (m : V n) (b : N)
    (u : projectiveGradedAway f V) (hu : u.val = projectiveGradedFraction f V n m) :
    (projectiveGradedTensorLocalizationMap (N := N) f V (u ⊗ₜ[R] b)).val =
      LocalizedModule.mk (m.val ⊗ₜ[R] b) (projDenominator f n) := by
  rw [projectiveGradedTensorLocalizationMap_val, LinearMap.rTensor_tmul]
  change (projectiveRightTensorLocalizationEquiv (R := R) (Submonoid.powers f)).symm
    (u.val ⊗ₜ[R] b) = _
  rw [hu, projectiveGradedFraction_apply]
  exact (projectiveRightTensorLocalizationEquiv
    (R := R) (Submonoid.powers f)).symm_apply_eq.mpr
      (projectiveRightTensorLocalizationEquiv_mk _ _ _ _).symm

/-- 指定次数の比較写像は全射。分子族のテンソル像の定義だけで成立する。 -/
theorem projectiveGradedTensorLocalizationMap_surjective :
    Function.Surjective (projectiveGradedTensorLocalizationMap (N := N) f V) := by
  let U := projectiveGradedAway f V
  let W := projectiveGradedAway f (projectiveTensorNumerator (N := N) V)
  let h : U ⊗[R] N →ₗ[R] LocalizedModule (Submonoid.powers f) (M ⊗[R] N) :=
    W.subtype.comp (projectiveGradedTensorLocalizationMap (N := N) f V)
  have hle : W ≤ LinearMap.range h := by
    apply iSup_le
    intro n x hx
    obtain ⟨m, rfl⟩ := hx
    obtain ⟨w, hw⟩ := m.property
    rw [projectiveGradedFraction_apply, ← hw]
    clear hw
    induction w using TensorProduct.inductionOn with
    | tmul v b =>
      let u : U := ⟨projectiveGradedFraction f V n v,
        (le_iSup (fun k ↦ LinearMap.range (projectiveGradedFraction f V k)) n)
          ⟨v, rfl⟩⟩
      exact ⟨u ⊗ₜ[R] b, projectiveGradedTensorLocalizationMap_fraction f V n v b u rfl⟩
    | add x y hx hy =>
      simpa only [map_add, projectiveLocalizedModule_mk_add] using
        (LinearMap.range h).add_mem hx hy
  intro z
  obtain ⟨w, hw⟩ := hle z.property
  exact ⟨w, Subtype.ext hw⟩

/-- flat な右テンソル積は、指定分子族の斉次局所化と交換する。 -/
def projectiveGradedTensorLocalizationEquiv [Module.Flat R N] :
    (projectiveGradedAway f V) ⊗[R] N ≃ₗ[R]
      projectiveGradedAway f (projectiveTensorNumerator (N := N) V) :=
  LinearEquiv.ofBijective (projectiveGradedTensorLocalizationMap (N := N) f V)
    ⟨projectiveGradedTensorLocalizationMap_injective f V,
      projectiveGradedTensorLocalizationMap_surjective f V⟩

end SerrePositivity.AlgebraicGeometry
