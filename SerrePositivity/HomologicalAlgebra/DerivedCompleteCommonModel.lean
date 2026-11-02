module

public import SerrePositivity.CommutativeAlgebra.Localization.CommonModel
public import SerrePositivity.CommutativeAlgebra.PerfectoidDerivedComplete
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.PrincipalIdeal
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.FinitePresentationComplete
public import SerrePositivity.CommutativeAlgebra.AbsolutelyIntegrallyClosed.Etale
public import SerrePositivity.CommutativeAlgebra.Localization.Away

/-! # 局所分裂の導来完備な共通模型

## 概要

integral perfectoid な `R` 上の有限表示な有限代数 `A` で、`d` を反転すると `L ⊗ A ≃ L^r` と分裂するものについて、`R` の作用と自身の環の作用を両方保つ導来完備な共通模型を作る（`localizationSplitting_exists_derivedComplete_common_model`）。絶対整閉な環の有限エタールな主局所化の被覆について、その上に同じ模型を選ぶ（`aic_finiteEtaleAway_exists_derivedComplete_common_cover`）。

## 方針

模型は perfectoid 化や Tor の検査より前に選ぶ。完備性は有限表示性と主イデアルの導来完備性から示す。

## 規約

BS Cor 8.12 の excision の四角は主張しない。旧 `CLMST/PerfectoidFinitePresentationCommonModel`・`PerfectoidEtaleCommonCover`（CLMST Prop 2.4.9(a)・Thm 4.0.3 の KL 比較の準備）。

## 使われ方

CLMST の KL 比較（`KLAicTorFromExcision`）。
-/

@[expose] public noncomputable section

universe u

section FinitePresentationCommonModelPart

namespace SerrePositivity
open DerivedCompletion
open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false

/-- A localized splitting over a perfectoid ring has a finite presentation common
model whose ring, principal closed ideal and closed quotient are derived p-complete.
Both actual finite maps retain their supported kernels and common cokernel bound. -/
theorem localizationSplitting_exists_derivedComplete_common_model
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    [Module.Finite R A] [Algebra.FinitePresentation R A]
    (p : ℕ) [Fact p.Prime] (hR : IsIntegralPerfectoid R p)
    (d : R) (L : Type u) [CommRing L] [Algebra R L] [IsLocalization (.powers d) L]
    (r : ℕ) (e : L ⊗[R] A ≃ₐ[L] (Fin r → L)) :
    ∃ (E : Type u) (_ : CommRing E) (_ : Algebra R E),
      Module.Finite R E ∧ Algebra.FinitePresentation R E ∧ Module.FinitePresentation R E ∧
      IsModuleComplete R (p : R) (ModuleCat.of R E) ∧
      IsModuleComplete E (p : E) (ModuleCat.of E E) ∧
      IsModuleComplete E (p : E) (ModuleCat.of E (Ideal.span {algebraMap R E d})) ∧
      IsModuleComplete (E ⧸ Ideal.span {algebraMap R E d})
        (p : E ⧸ Ideal.span {algebraMap R E d})
        (ModuleCat.of (E ⧸ Ideal.span {algebraMap R E d})
          (E ⧸ Ideal.span {algebraMap R E d})) ∧
      ∃ (u : A →ₐ[R] E) (v : (Fin r → R) →ₐ[R] E) (w : E →ₐ[R] (Fin r → L)),
        (∀ a, w (u a) = e ((1 : L) ⊗ₜ[R] a)) ∧
        (∀ b i, w (v b) i = algebraMap R L (b i)) ∧
        IsLocalizedModule (.powers d) w.toLinearMap ∧
        u.toRingHom.Finite ∧ v.toRingHom.Finite ∧
        (∀ a, u a = 0 → ∃ n : ℕ, d ^ n • a = 0) ∧
        (∀ b, v b = 0 → ∃ n : ℕ, d ^ n • b = 0) ∧
        ∃ n : ℕ, (∀ y : E ⧸ u.toLinearMap.range, d ^ n • y = 0) ∧
          (∀ y : E ⧸ v.toLinearMap.range, d ^ n • y = 0) := by
  obtain ⟨E, hE, aE, hfinite, hfp, hmfp, maps⟩ :=
    localizationSplitting_exists_finitePresentation_common_model_bounds d L r e
  let : Module.FinitePresentation R E := hmfp
  have hcomplete := isModuleComplete_finitePresentation_algebra_principal R E
    (p : R) (algebraMap R E d) (hR.isModuleComplete R p)
  simp only [map_natCast] at hcomplete
  exact ⟨E, hE, aE, hfinite, hfp, hmfp, hcomplete.1, hcomplete.2.1,
    hcomplete.2.2.1, hcomplete.2.2.2, maps⟩

end SerrePositivity

end FinitePresentationCommonModelPart

section EtaleCommonCoverPart

namespace SerrePositivity
open DerivedCompletion
open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false

/-- The actual finite splitting cover off g has finite presentation, derived
p-complete common models with both original finite maps and supported errors.
The two tensor maps are bijective, and the rank may vary with the cover member. -/
theorem aic_finiteEtaleAway_exists_derivedComplete_common_cover
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    [Module.Finite R A] [Algebra.FinitePresentation R A]
    (p : ℕ) [Fact p.Prime] (hR : IsIntegralPerfectoid R p)
    (hAIC : IsAbsolutelyIntegrallyClosed R) (g : R) :
    letI := GenericEtale.awayAlgebra R A g
    Algebra.Etale (Localization.Away g) (Localization.Away (algebraMap R A g)) →
      ∃ t : Finset (Localization.Away g),
        Ideal.span (t : Set (Localization.Away g)) = ⊤ ∧
        (∃ N : ℕ, g ^ N ∈ Ideal.span (Set.range (fun f : t =>
          g * (IsLocalization.Away.sec g f.1).1))) ∧
        ∀ f ∈ t, ∃ (r : ℕ)
          (e : (Localization.Away f) ⊗[Localization.Away g]
            (Localization.Away (algebraMap R A g)) ≃ₐ[Localization.Away f]
              (Fin r → Localization.Away f))
          (E : Type u) (_ : CommRing E) (_ : Algebra R E),
          Module.Finite R E ∧ Algebra.FinitePresentation R E ∧ Module.FinitePresentation R E ∧
          IsModuleComplete R (p : R) (ModuleCat.of R E) ∧
          IsModuleComplete E (p : E) (ModuleCat.of E E) ∧
          IsModuleComplete E (p : E) (ModuleCat.of E
            (Ideal.span {algebraMap R E (g * (IsLocalization.Away.sec g f).1)})) ∧
          IsModuleComplete (E ⧸ Ideal.span {algebraMap R E (g * (IsLocalization.Away.sec g f).1)})
            (p : E ⧸ Ideal.span {algebraMap R E (g * (IsLocalization.Away.sec g f).1)})
            (ModuleCat.of (E ⧸ Ideal.span {algebraMap R E (g * (IsLocalization.Away.sec g f).1)})
              (E ⧸ Ideal.span {algebraMap R E (g * (IsLocalization.Away.sec g f).1)})) ∧
          ∃ (u : A →ₐ[R] E) (v : (Fin r → R) →ₐ[R] E)
            (w : E →ₐ[R] (Fin r → Localization.Away f)),
            (∀ a, w (u a) = e ((1 : Localization.Away f) ⊗ₜ[Localization.Away g]
              algebraMap A (Localization.Away (algebraMap R A g)) a)) ∧
            (∀ b i, w (v b) i = algebraMap R (Localization.Away f) (b i)) ∧
            IsLocalizedModule (.powers (g * (IsLocalization.Away.sec g f).1)) w.toLinearMap ∧
            u.toRingHom.Finite ∧ v.toRingHom.Finite ∧
            Function.Bijective (Algebra.TensorProduct.map
              (AlgHom.id (Localization.Away f) (Localization.Away f)) u) ∧
            Function.Bijective (Algebra.TensorProduct.map
              (AlgHom.id (Localization.Away f) (Localization.Away f)) v) ∧
            (∀ a, u a = 0 → ∃ n : ℕ, (g * (IsLocalization.Away.sec g f).1) ^ n • a = 0) ∧
            (∀ b, v b = 0 → ∃ n : ℕ, (g * (IsLocalization.Away.sec g f).1) ^ n • b = 0) ∧
            ∃ n : ℕ,
              (∀ y : E ⧸ u.toLinearMap.range, (g * (IsLocalization.Away.sec g f).1) ^ n • y = 0) ∧
              (∀ y : E ⧸ v.toLinearMap.range,
                (g * (IsLocalization.Away.sec g f).1) ^ n • y = 0) := by
  let := GenericEtale.awayAlgebra R A g
  intro hetale
  obtain ⟨t, ht, hsplit, hcover⟩ := hAIC.finiteEtaleAway_exists_finite_cover g hetale
  refine ⟨t, ht, hcover, ?_⟩
  intro f hf
  obtain ⟨r, ⟨e⟩⟩ := hsplit f hf
  let d := g * (IsLocalization.Away.sec g f).1
  let : IsLocalization (.powers d) (Localization.Away f) :=
    principalLocalizationTower_isLocalization g f
  let e' := (doubleLocalizationTensorEquiv R A g f).trans e
  obtain ⟨E, hE, aE, hfinite, hfp, hmfp, hcR, hcE, hcI, hcQ,
    u, v, w, hu, hv, hloc, huF, hvF, huk, hvk, n, huc, hvc⟩ :=
    localizationSplitting_exists_derivedComplete_common_model p hR d (Localization.Away f) r e'
  let : IsLocalizedModule (.powers d) w.toLinearMap := hloc
  obtain ⟨htu, htv⟩ := localizationSplitting_common_model_tensorMaps_bijective
    (.powers d) (Localization.Away f) r e' u v w hu hv
  refine ⟨r, e, E, hE, aE, hfinite, hfp, hmfp, hcR, hcE, hcI, hcQ,
    u, v, w, ?_, hv, hloc, huF, hvF, htu, htv, huk, hvk, n, huc, hvc⟩
  intro a
  rw [hu]
  change e (doubleLocalizationTensorEquiv R A g f ((1 : Localization.Away f) ⊗ₜ[R] a)) = _
  rw [doubleLocalizationTensorEquiv_tmul]

end SerrePositivity

end EtaleCommonCoverPart
