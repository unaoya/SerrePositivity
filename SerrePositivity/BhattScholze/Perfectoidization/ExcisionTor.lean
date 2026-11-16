module

public import SerrePositivity.BhattScholze.Perfectoidization.SupportedQuotient
public import SerrePositivity.BhattScholze.PerfectoidIdeal.CompletedQuotient
public import SerrePositivity.CommutativeAlgebra.Localization.PowerTorsion
public import SerrePositivity.BhattScholze.Prism.Perfectoid.FiniteProduct
public import SerrePositivity.CommutativeAlgebra.Localization.CommonModel
public import SerrePositivity.BhattScholze.Perfectoidization.ExcisionComparison

/-! # 標準 excision の四角からの Tor の入力

## 概要

局所化の像の perfectoid 化との実際の Tor 比較（核の台は元の局所化写像から得る）、有限直積の脚とその台つきの像の Tor の入力（自由な源は元の普遍単位で同定する）を与え、二つの指定した標準 excision の四角から perfectoid イデアルの局所的な Tor の入力を得る（`perfectoidIdeal_powerTorsionTorInput_of_two_canonical_excision`）。

## 方針

すべての単位と比較写像を、検査加群・指数・次数・イデアルの元より前に固定する。

## 規約

二つの引き戻しの主張は明示的な入力のまま残す。BS 著者版 Corollary 8.12 を供給したり導来模型を同定したりはしない。旧 `CLMST/PerfectoidizationImageTorComparison`・`PerfectoidFiniteProductTor`・`CanonicalExcisionTorInput`。

## 使われ方

CLMST の KL 比較（`KLAicTorFromExcision`）。
-/

@[expose] public noncomputable section

universe u

section PerfectoidizationImageTorComparisonPart

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open _root_.CategoryTheory
variable {R A E C D : Type u}
    [CommRing R] [CommRing A] [CommRing E] [CommRing C] [CommRing D]
    [Algebra R A] [Algebra R E] [Algebra R C] [Algebra R D]
    {p : ℕ} [Fact p.Prime] {f : A →ₐ[R] C}

/-- Actual source-to-image comparison preserves all original ideal Tor tests. -/
theorem perfectoidIdeal_TorInput_iff_image
    (hR : IsIntegralPerfectoid R p) (φ : A →ₐ[R] E)
    (hf : IsPerfectoidization p f.toRingHom)
    (g : φ.range →ₐ[R] D) (hg : IsPerfectoidization p g.toRingHom)
    (ρ : ℕ → R) (hρ : ∀ n, ρ (n + 1) ^ p = ρ n)
    (hk : ∀ a, φ a = 0 → ∃ e : ℕ, ρ 0 ^ e • a = 0)
    (N : ModuleCat.{u} R) (k : ℕ) (hN : ∀ x : N, (p : R) ^ k • x = 0) (i : ℕ) :
    (∀ s ∈ _root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal R p hR (ρ 0),
      torCoefficientScalarEndomorphism C N i (algebraMap R C s) = 0) ↔
    (∀ s ∈ _root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal R p hR (ρ 0),
      torCoefficientScalarEndomorphism D N i (algebraMap R D s) = 0) := by
  obtain ⟨hker, hcoker⟩ :=
    _root_.SerrePositivity.BhattScholze.Perfectoidization.perfectoidization_image_ker_coker_annihilated hR φ hf g hg ρ hρ hk
  exact torCoefficientIdeal_eq_zero_iff_of_almost_comparison
    (IsPerfectoidization.mapAlgHom hf hg φ.rangeRestrict).toLinearMap
    (_root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal R p hR (ρ 0)) hker hcoker N ((p : R) ^ k) hN
    (_root_.SerrePositivity.BhattScholze.Almost.perfectoidIdealMod_idempotent R p hR (ρ 0) k) i

/-- An ordinary localization comparison supplies an actual image target once,
with all Tor tests preserved; no almost kernel hypothesis is assumed. -/
theorem exists_localization_image_perfectoidization_Tor_comparison
    [Module.Finite R A] (hR : IsIntegralPerfectoid R p)
    (ρ : ℕ → R) (hρ : ∀ n, ρ (n + 1) ^ p = ρ n)
    (φ : A →ₐ[R] E) (hf : IsPerfectoidization p f.toRingHom)
    {X : Type u} [AddCommGroup X] [Module R X]
    (α : A →ₗ[R] X) [IsLocalizedModule (.powers (ρ 0)) α]
    (j : E →ₗ[R] X) (hcomm : j.comp φ.toLinearMap = α) :
    ∃ (D : Type u) (_ : CommRing D) (_ : Algebra R D) (g : φ.range →ₐ[R] D),
      IsPerfectoidization p g.toRingHom ∧
      ∀ (N : ModuleCat.{u} R) (k : ℕ), (∀ x : N, (p : R) ^ k • x = 0) → ∀ i : ℕ,
        (∀ s ∈ _root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal R p hR (ρ 0),
          torCoefficientScalarEndomorphism C N i (algebraMap R C s) = 0) ↔
        (∀ s ∈ _root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal R p hR (ρ 0),
          torCoefficientScalarEndomorphism D N i (algebraMap R D s) = 0) := by
  have hk : ∀ a, φ a = 0 → ∃ e : ℕ, ρ 0 ^ e • a = 0 :=
    localizationComparison_ker_power_torsion (ρ 0) φ.toLinearMap α j hcomm
  obtain ⟨D, hD, hDalg, g, hg, _⟩ :=
    _root_.SerrePositivity.BhattScholze.Perfectoidization.exists_image_perfectoidization_almost_comparison hR φ hf ρ hρ hk
  let := hD
  let := hDalg
  exact ⟨D, hD, hDalg, g, hg,
    fun N k hN i => perfectoidIdeal_TorInput_iff_image hR φ hf g hg ρ hρ hk N k hN i⟩

end SerrePositivity.BhattScholze

end PerfectoidizationImageTorComparisonPart

section PerfectoidFiniteProductTorPart

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open _root_.CategoryTheory _root_.CategoryTheory.Limits
open scoped _root_.TensorProduct

/-- Any specified perfectoidization of the finite product has its original
finite-free module structure over R, and in particular is flat. -/
theorem finiteProduct_perfectoidization_flat
    (R : Type u) [CommRing R] (p : ℕ) [Fact p.Prime]
    (hR : IsIntegralPerfectoid R p) (r : ℕ)
    (C : Type u) [CommRing C] [Algebra R C]
    (f : (Fin r → R) →ₐ[R] C) (hf : IsPerfectoidization p f.toRingHom) :
    Module.Flat R C := by
  obtain ⟨e, _⟩ := BhattScholze.finiteProduct_perfectoidization_exists_algEquiv R p hR r C f hf
  exact Module.Flat.of_linearEquiv e.symm.toLinearEquiv

/-- Every coefficient endomorphism in positive Tor is zero for the actual
perfectoidization of R^r, even for test modules with no torsion hypothesis. -/
theorem finiteProduct_perfectoidization_Tor_zero
    (R : Type u) [CommRing R] (p : ℕ) [Fact p.Prime]
    (hR : IsIntegralPerfectoid R p) (r : ℕ)
    (C : Type u) [CommRing C] [Algebra R C]
    (f : (Fin r → R) →ₐ[R] C) (hf : IsPerfectoidization p f.toRingHom)
    (N : ModuleCat.{u} R) (i : ℕ) (hi : 0 < i) (c : C) :
    torCoefficientScalarEndomorphism C N i c = 0 := by
  let := finiteProduct_perfectoidization_flat R p hR r C f hf
  have hz : IsZero (((Tor (ModuleCat.{u} R) i).obj (ModuleCat.of R C)).obj N) := by
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hi)
    exact ModuleCat.isZero_iff_subsingleton.mpr
      (torModule_subsingleton_of_flat (R := R) C N j)
  exact hz.eq_of_src _ _

/-- The supported actual image of the finite-product leg has the full original
ideal Tor input. The image target is fixed before all test modules and degrees. -/
theorem supported_finiteProduct_image_powerTorsionTorInput
    {R E D : Type u} [CommRing R] [CommRing E] [CommRing D]
    [Algebra R E] [Algebra R D] {p : ℕ} [Fact p.Prime]
    (hR : IsIntegralPerfectoid R p) (r : ℕ) (φ : (Fin r → R) →ₐ[R] E)
    (g : φ.range →ₐ[R] D) (hg : IsPerfectoidization p g.toRingHom)
    (ρ : ℕ → R) (hρ : ∀ n, ρ (n + 1) ^ p = ρ n)
    (hk : ∀ a, φ a = 0 → ∃ e : ℕ, ρ 0 ^ e • a = 0) :
    ∀ (N : ModuleCat.{u} R) (k : ℕ), (∀ x : N, (p : R) ^ k • x = 0) →
      ∀ i : ℕ, 0 < i → ∀ s ∈ _root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal R p hR (ρ 0),
        torCoefficientScalarEndomorphism D N i (algebraMap R D s) = 0 := by
  let f : (Fin r → R) →ₐ[R] (Fin r → R) := AlgHom.id R (Fin r → R)
  have hf : IsPerfectoidization p f.toRingHom :=
    (BhattScholze.isIntegralPerfectoid_finPi R p hR r).isPerfectoidization_id
  intro N k hN i hi s hs
  have hiff := perfectoidIdeal_TorInput_iff_image hR φ hf g hg ρ hρ hk N k hN i
  exact hiff.mp (fun t _ =>
    finiteProduct_perfectoidization_Tor_zero R p hR r (Fin r → R) f hf N i hi
      (algebraMap R (Fin r → R) t)) s hs

/-- The actual finite common model of a localized splitting has a finite-product
image perfectoidization with all original positive Tor actions almost zero. -/
theorem localizationSplitting_exists_finiteProduct_image_TorInput
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A] [Module.Finite R A]
    {p : ℕ} [Fact p.Prime] (hR : IsIntegralPerfectoid R p)
    (ρ : ℕ → R) (hρ : ∀ n, ρ (n + 1) ^ p = ρ n)
    (L : Type u) [CommRing L] [Algebra R L] [IsLocalization (.powers (ρ 0)) L]
    (r : ℕ) (e : L ⊗[R] A ≃ₐ[L] (Fin r → L)) :
    ∃ E : Subalgebra R (Fin r → L), Module.Finite R E ∧
      ∃ (u : A →ₐ[R] E) (v : (Fin r → R) →ₐ[R] E),
        (∀ a, E.val (u a) = e ((1 : L) ⊗ₜ[R] a)) ∧
        (∀ b i, E.val (v b) i = algebraMap R L (b i)) ∧
        ∃ (D : Type u) (_ : CommRing D) (_ : Algebra R D) (g : v.range →ₐ[R] D),
          IsPerfectoidization p g.toRingHom ∧
          ∀ (N : ModuleCat.{u} R) (k : ℕ), (∀ x : N, (p : R) ^ k • x = 0) →
            ∀ i : ℕ, 0 < i → ∀ s ∈ _root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal R p hR (ρ 0),
              torCoefficientScalarEndomorphism D N i (algebraMap R D s) = 0 := by
  obtain ⟨E, hE, _hloc, u, v, hu, hv, _huF, _hvF, _huk, hvk, _⟩ :=
    localizationSplitting_exists_finite_common_model_bounds (ρ 0) L r e
  let f : (Fin r → R) →ₐ[R] (Fin r → R) := AlgHom.id R (Fin r → R)
  have hf : IsPerfectoidization p f.toRingHom :=
    (BhattScholze.isIntegralPerfectoid_finPi R p hR r).isPerfectoidization_id
  obtain ⟨D, hD, hDalg, g, hg, _⟩ :=
    _root_.SerrePositivity.BhattScholze.Perfectoidization.exists_image_perfectoidization_almost_comparison hR v hf ρ hρ hvk
  let := hD
  let := hDalg
  exact ⟨E, hE, u, v, hu, hv, D, hD, hDalg, g, hg,
    supported_finiteProduct_image_powerTorsionTorInput hR r v g hg ρ hρ hvk⟩

end SerrePositivity.BhattScholze

end PerfectoidFiniteProductTorPart

section CanonicalExcisionTorInputPart

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.SerrePositivity.BhattScholze

/-- The two actual canonical excision squares transfer all original ideal Tor
tests from the finite free source through E to A. No almost comparison or
Tor-zero hypothesis is supplied by the caller. -/
theorem perfectoidIdeal_powerTorsionTorInput_of_two_canonical_excision
    {R A E C D F : Type u} [CommRing R] [CommRing A] [CommRing E]
    [CommRing C] [CommRing D] [CommRing F]
    [Algebra R A] [Algebra R E] [Algebra R C] [Algebra R D] [Algebra R F]
    (p : ℕ) [Fact p.Prime] (hR : IsIntegralPerfectoid R p) (a : R) (r : ℕ)
    (u : A →ₐ[R] E) (v : (Fin r → R) →ₐ[R] E)
    (f : A →ₐ[R] C) (g : E →ₐ[R] D) (h : (Fin r → R) →ₐ[R] F)
    (hf : IsPerfectoidization p f.toRingHom) (hg : IsPerfectoidization p g.toRingHom)
    (hh : IsPerfectoidization p h.toRingHom)
    (hPBu : IsPullback
      (CommRingCat.ofHom (IsPerfectoidization.map hf hg u.toRingHom))
      (CommRingCat.ofHom (perfectoidizationClosedSideProjection hf
        (Ideal.span {algebraMap R A a})))
      (CommRingCat.ofHom (perfectoidizationClosedSideProjection hg
        ((Ideal.span {algebraMap R A a}).map u.toRingHom)))
      (CommRingCat.ofHom (perfectoidizationClosedComparison hf hg u.toRingHom
        (Ideal.span {algebraMap R A a}))))
    (hPBv : IsPullback
      (CommRingCat.ofHom (IsPerfectoidization.map hh hg v.toRingHom))
      (CommRingCat.ofHom (perfectoidizationClosedSideProjection hh
        (Ideal.span {algebraMap R (Fin r → R) a})))
      (CommRingCat.ofHom (perfectoidizationClosedSideProjection hg
        ((Ideal.span {algebraMap R (Fin r → R) a}).map v.toRingHom)))
      (CommRingCat.ofHom (perfectoidizationClosedComparison hh hg v.toRingHom
        (Ideal.span {algebraMap R (Fin r → R) a})))) :
    ∀ (N : ModuleCat.{u} R) (k : ℕ), (∀ x : N, (p : R) ^ k • x = 0) →
      ∀ i : ℕ, 0 < i → ∀ s ∈ _root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal R p hR a,
        torCoefficientScalarEndomorphism C N i (algebraMap R C s) = 0 := by
  obtain ⟨huk, huc⟩ :=
    BhattScholze.perfectoidization_comparison_almost_of_canonical_excision hR hf hg u a hPBu
  obtain ⟨hvk, hvc⟩ :=
    BhattScholze.perfectoidization_comparison_almost_of_canonical_excision hR hh hg v a hPBv
  have hfree : ∀ (N : ModuleCat.{u} R) (k : ℕ), (∀ x : N, (p : R) ^ k • x = 0) →
      ∀ i : ℕ, 0 < i → ∀ s ∈ _root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal R p hR a,
        torCoefficientScalarEndomorphism F N i (algebraMap R F s) = 0 := by
    intro N _ _ i hi s _
    exact finiteProduct_perfectoidization_Tor_zero R p hR r F h hh N i hi
      (algebraMap R F s)
  have hD := (perfectoidIdeal_powerTorsionTorInput_iff_of_almost_comparison R p hR a F D
    (IsPerfectoidization.mapAlgHom hh hg v).toLinearMap hvk hvc).mp hfree
  exact (perfectoidIdeal_powerTorsionTorInput_iff_of_almost_comparison R p hR a C D
    (IsPerfectoidization.mapAlgHom hf hg u).toLinearMap huk huc).mpr hD

end SerrePositivity.BhattScholze

end CanonicalExcisionTorInputPart
