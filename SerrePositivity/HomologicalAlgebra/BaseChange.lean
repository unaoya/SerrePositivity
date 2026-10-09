module

public import SerrePositivity.HomologicalAlgebra.Basic
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.LinearAlgebra.TensorProduct.Tower

/-!
# 複体の係数拡大

- 係数拡大関手 `ModuleCat.extendScalars φ` は加法的（複体に施すため、また左導来関手をとるために要る）。
- `baseChange φ P = P ⊗_T C`：環準同型 `φ : T →+* C` に沿った係数拡大を、各項に施したもの。
  有界性・正の次数での零を保つ。
- 係数拡大はスカラー倍を `φ` 倍に送る（`extendScalars_map_smul` など）。
-/

@[expose] public section

universe u

open CategoryTheory Limits
open scoped ChangeOfRings

namespace SerrePositivity

section

variable {T C : Type u} [CommRing T] [CommRing C]

/-- 係数拡大関手は（係数制限関手の左随伴なので）加法的。 -/
instance (φ : T →+* C) : (ModuleCat.extendScalars.{u, u, u} φ).Additive :=
  (ModuleCat.extendRestrictScalarsAdj φ).left_adjoint_additive

/-- 係数拡大 `P ⊗_T C`（`φ : T →+* C` に沿って）。 -/
noncomputable abbrev baseChange (φ : T →+* C) (P : CochainComplex (ModuleCat.{u} T) ℤ) :
    CochainComplex (ModuleCat.{u} C) ℤ :=
  ((ModuleCat.extendScalars.{u, u, u} φ).mapHomologicalComplex _).obj P

/-- 係数拡大は複体の有界性を保つ。 -/
lemma baseChange_bounded (φ : T →+* C) (P : CochainComplex (ModuleCat.{u} T) ℤ)
    (hP : ∃ a b : ℤ, ∀ i, (i < a ∨ b < i) → IsZero (P.X i)) :
    ∃ a b : ℤ, ∀ i, (i < a ∨ b < i) → IsZero ((baseChange φ P).X i) := by
  obtain ⟨a, b, hab⟩ := hP
  exact ⟨a, b, fun i hi ↦ (ModuleCat.extendScalars φ).map_isZero (hab i hi)⟩

/-- 基底変更した複体も正の次数で零。 -/
lemma baseChange_isZero_X_of_pos (φ : T →+* C) (K : CochainComplex (ModuleCat.{u} T) ℤ)
    (hK : ∀ i : ℤ, 0 < i → IsZero (K.X i)) (i : ℤ) (hi : 0 < i) :
    IsZero ((baseChange φ K).X i) :=
  (ModuleCat.extendScalars.{u, u, u} φ).map_isZero (hK i hi)

end

variable {A C : Type u} [CommRing A] [CommRing C] (φ : A →+* C)

/-- 係数拡大は射のスカラー倍を `φ` 倍に送る。 -/
lemma extendScalars_map_smul {M N : ModuleCat.{u} A} (f : M ⟶ N) (a : A) :
    (ModuleCat.extendScalars.{u, u, u} φ).map (a • f) =
      φ a • (ModuleCat.extendScalars.{u, u, u} φ).map f := by
  ext m
  change ((1 : C) ⊗ₜ[A, φ] (a • f m) : (ModuleCat.extendScalars φ).obj N) =
    (φ a * 1) ⊗ₜ[A, φ] f m
  let _ : Module A C := Module.compHom C φ
  change (1 : C) ⊗ₜ[A] (a • f m) = (φ a * 1) ⊗ₜ[A] f m
  rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul']
  rfl

/-- 係数拡大は複体の射のスカラー倍を `φ` 倍に送る（任意の複体の形）。 -/
lemma extendScalars_mapHomologicalComplex_smul {ι : Type*} {c : ComplexShape ι}
    {K L : HomologicalComplex (ModuleCat.{u} A) c} (f : K ⟶ L) (a : A) :
    ((ModuleCat.extendScalars.{u, u, u} φ).mapHomologicalComplex c).map (a • f) =
      φ a • ((ModuleCat.extendScalars.{u, u, u} φ).mapHomologicalComplex c).map f := by
  ext i
  simp [extendScalars_map_smul]

/-- 係数拡大は `a • 𝟙 K` を `φ a • 𝟙` に送る。 -/
lemma baseChange_smulId (K : CochainComplex (ModuleCat.{u} A) ℤ) (a : A) :
    ((ModuleCat.extendScalars.{u, u, u} φ).mapHomologicalComplex _).map (smulId a K) =
      smulId (φ a) (baseChange φ K) := by
  ext i
  simp [smulId, extendScalars_map_smul]

end SerrePositivity
