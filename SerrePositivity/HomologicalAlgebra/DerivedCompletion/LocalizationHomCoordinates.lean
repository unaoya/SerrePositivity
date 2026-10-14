module

public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.LocalizationResolution
public import SerrePositivity.HomologicalAlgebra.HomComplexCone

/-! # 局所化の二項自由分解からのHom複体の列座標 -/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.DerivedCompletion
open CategoryTheory HomologicalComplex CochainComplex.HomComplex
variable (R : Type u) [CommRing R]

/-- 自由telescopeを零次数に置いた複体からのcochainを、自由基底で評価する。 -/
def localizationFreeCochainEquiv (K : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ) :
    Cochain ((CochainComplex.singleFunctor (ModuleCat R) 0).obj
      (ModuleCat.of R (LocalizationTelescopeFree R))) K n ≃ₗ[R] (ℕ → K.X n) :=
  Cochain.fromSingleLinearEquiv (zero_add n) ≪≫ₗ
    ModuleCat.homLinearEquiv ≪≫ₗ localizationTelescopeHomEquiv R (K.X n)

/-- 自由基底の評価を、零次数から作った標準cochainについて計算する。 -/
@[simp] theorem localizationFreeCochainEquiv_fromSingleMk
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ)
    (f : ModuleCat.of R (LocalizationTelescopeFree R) ⟶ K.X n) :
    localizationFreeCochainEquiv R K n (Cochain.fromSingleMk f (zero_add n)) =
      localizationTelescopeHomEquiv R (K.X n) f.hom := by
  simp [localizationFreeCochainEquiv, Cochain.fromSingleLinearEquiv]
  rfl

/-- 自由基底の評価は、Hom複体の微分をKの成分ごとの微分へ移す。 -/
theorem localizationFreeCochainEquiv_δ (K : CochainComplex (ModuleCat.{u} R) ℤ)
    (n p : ℤ) (x : Cochain ((CochainComplex.singleFunctor (ModuleCat R) 0).obj
      (ModuleCat.of R (LocalizationTelescopeFree R))) K n) :
    localizationFreeCochainEquiv R K p (δ n p x) =
      fun k ↦ K.d n p (localizationFreeCochainEquiv R K n x k) := by
  obtain ⟨f, rfl⟩ := Cochain.fromSingleMk_surjective x n (zero_add n)
  rw [Cochain.δ_fromSingleMk f (zero_add n) p p (zero_add p)]
  rw [localizationFreeCochainEquiv_fromSingleMk, localizationFreeCochainEquiv_fromSingleMk]
  rfl

/-- Telescopeの差分に沿う前合成は、列のa進差分へ移る。 -/
theorem localizationFreeCochainEquiv_precomp (a : R)
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ)
    (x : Cochain ((CochainComplex.singleFunctor (ModuleCat R) 0).obj
      (ModuleCat.of R (LocalizationTelescopeFree R))) K n) :
    localizationFreeCochainEquiv R K n
      ((Cochain.ofHom (localizationPresentationComplex R a).f).comp x (zero_add n)) =
        adicRecurrenceMap a (localizationFreeCochainEquiv R K n x) := by
  obtain ⟨f, rfl⟩ := Cochain.fromSingleMk_surjective x n (zero_add n)
  change localizationFreeCochainEquiv R K n
    ((Cochain.ofHom ((CochainComplex.singleFunctor (ModuleCat R) 0).map
      (ModuleCat.ofHom (localizationTelescopeMap R a)))).comp
        (Cochain.fromSingleMk f (zero_add n)) (zero_add n)) = _
  rw [← Cochain.fromSingleMk_precomp]
  rw [localizationFreeCochainEquiv_fromSingleMk, localizationFreeCochainEquiv_fromSingleMk]
  exact localizationTelescopeHomEquiv_comp R a (K.X n) f.hom

/-- 二項自由分解からのHomの次数n成分を、隣接二次数の列の組へ同定する。 -/
def localizationResolutionCochainEquiv (a : R) (K : CochainComplex (ModuleCat.{u} R) ℤ)
    (m n : ℤ) (h : m + 1 = n) :
    Cochain (localizationResolutionComplex R a) K n ≃ₗ[R]
      (ℕ → K.X m) × (ℕ → K.X n) :=
  mappingConeSourceCochainEquiv R (localizationPresentationComplex R a).f K m n h ≪≫ₗ
    (localizationFreeCochainEquiv R K m).prodCongr (localizationFreeCochainEquiv R K n)

/-- 列の二成分から、元のHom複体のcochainを組み立てる。 -/
theorem localizationResolutionCochainEquiv_symm_apply (a : R)
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (m n : ℤ) (h : m + 1 = n)
    (α : ℕ → K.X m) (β : ℕ → K.X n) :
    (localizationResolutionCochainEquiv R a K m n h).symm (α, β) =
      (mappingConeSourceCochainEquiv R (localizationPresentationComplex R a).f K m n h).symm
        ((localizationFreeCochainEquiv R K m).symm α,
          (localizationFreeCochainEquiv R K n).symm β) := rfl

/-- 列表示でのHom複体の微分。符号付きのa進差分を含む。 -/
theorem localizationResolutionCochainEquiv_symm_δ (a : R)
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (m n p : ℤ)
    (h : m + 1 = n) (h' : n + 1 = p) (α : ℕ → K.X m) (β : ℕ → K.X n) :
    δ n p ((localizationResolutionCochainEquiv R a K m n h).symm (α, β)) =
      (localizationResolutionCochainEquiv R a K n p h').symm
        ((fun k ↦ K.d m n (α k)) + p.negOnePow • adicRecurrenceMap a β,
          fun k ↦ K.d n p (β k)) := by
  rw [localizationResolutionCochainEquiv_symm_apply,
    mappingConeSourceCochainEquiv_symm_δ R (localizationPresentationComplex R a).f K m n p h h',
    localizationResolutionCochainEquiv_symm_apply]
  congr 1
  apply Prod.ext
  · apply (localizationFreeCochainEquiv R K n).injective
    simp [localizationFreeCochainEquiv_δ, localizationFreeCochainEquiv_precomp,
      Units.smul_def]
  · apply (localizationFreeCochainEquiv R K p).injective
    simp [localizationFreeCochainEquiv_δ]

end SerrePositivity.DerivedCompletion
