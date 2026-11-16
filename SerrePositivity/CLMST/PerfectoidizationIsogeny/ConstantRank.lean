module

public import SerrePositivity.BhattScholze.Prism.Perfectoid.FiniteProduct
public import SerrePositivity.HomologicalAlgebra.FiniteFreeComparison
public import SerrePositivity.CLMST.PerfectoidizationIsogeny.Descent.Uniform
public import SerrePositivity.BhattScholze.Perfectoidization.FiniteComparisonExcision
public import SerrePositivity.CommutativeAlgebra.RankLocus
public import SerrePositivity.HomologicalAlgebra.ScalarConeAnnihilators

/-! # 定数階数の場合の錐の零化

## 概要

局所分裂と perfectoid 化の比較から実際の錐の零化を得て（`fixed_cone_of_localized_splitting`）、二つの標準 excision の四角からその入力を供給し、定数階数の被覆について元の写像の錐の零化を組み立てる（`aic_constantRank_isogeny_of_finiteComparison_excision`）。

## 方針

局所自由な比較と可換図式を構成し、残る入力を共通模型の二つの perfectoid 化比較の almost 零化にする。共通模型は HomologicalAlgebra/DerivedCompleteCommonModel。

## 規約

CLMST Prop 2.4.7 の定数階数の場合。excision の四角の引き戻し性は明示的な入力。旧 `CLMST/Prop247LocalComparison`・`Prop247ExcisionLocal`・`Prop247ConstantRankExcision`。

## 使われ方

`Rank/ComponentExcision`。
-/

@[expose] public noncomputable section

universe u

section Prop247LocalComparisonPart

namespace SerrePositivity.CLMST
open scoped _root_.TensorProduct
set_option backward.isDefEq.respectTransparency false

/-- 実共通モデルとその元の perfectoid 化比較の almost 零化から、元の β の錐を零化する。
有限自由比較や共通図式の可換性は仮定せず、元の局所分裂から構成する。 -/
theorem fixed_cone_of_localized_splitting
    {R A E P Q : Type u} [CommRing R] [IsReduced R] [CommRing A] [CommRing E]
    [CommRing P] [CommRing Q] [Algebra R A] [Algebra R E] [Algebra R P] [Algebra R Q]
    [Module.Finite R A] [Algebra.FinitePresentation R A]
    (p : ℕ) [Fact p.Prime]
    (β : A →ₐ[R] P) (hβ : IsPerfectoidization p β.toRingHom)
    (η : E →ₐ[R] Q) (hη : IsPerfectoidization p η.toRingHom)
    (d : R) (L : Type u) [CommRing L] [Algebra R L] [IsLocalization (.powers d) L]
    (r : ℕ) (e : L ⊗[R] A ≃ₐ[L] (Fin r → L))
    (a : A →ₐ[R] E) (b : (Fin r → R) →ₐ[R] E)
    (l : E →ₐ[R] (Fin r → L)) [IsLocalizedModule (.powers d) l.toLinearMap]
    (ha : ∀ x, l (a x) = e ((1 : L) ⊗ₜ[R] x))
    (hb : ∀ z i, l (b z) i = algebraMap R L (z i))
    (hv : ∀ y : P, IsPerfectoidization.mapAlgHom hβ hη a y = 0 → d • y = 0)
    (hw : ∀ z : (Fin r → R), η (b z) = 0 → d • z = 0)
    (hcw : ∀ y : Q ⧸ (η.comp b).toLinearMap.range, d • y = 0) :
    ∃ q : ℕ, moduleMapConeScalar R β.toLinearMap (d ^ q) = 0 := by
  obtain ⟨k, u, hsq, hu, _hq⟩ := exists_perfectoid_common_square
    p β hβ η hη d L r e a b l ha hb
  exact fixed_cone_of_scaled_common_comparison d r β.toLinearMap u
    (IsPerfectoidization.mapAlgHom hβ hη a).toLinearMap (η.comp b).toLinearMap
    k hsq hu hv hw hcw

end SerrePositivity.CLMST

end Prop247LocalComparisonPart

section Prop247ExcisionLocalPart

namespace SerrePositivity.CLMST
open _root_.SerrePositivity.BhattScholze
open scoped _root_.TensorProduct
set_option backward.isDefEq.respectTransparency false

/-- KL の二つの元の canonical 四角形から元の β の錐を冪零化する。
perfectoid 化対象・局所分裂・共通モデルは全て指定データとして保持する。 -/
theorem fixed_cone_of_two_canonical_excision
    {R A E P Q : Type u} [CommRing R] [CommRing A] [CommRing E]
    [CommRing P] [CommRing Q] [Algebra R A] [Algebra R E] [Algebra R P] [Algebra R Q]
    [Module.Finite R A] [Algebra.FinitePresentation R A]
    (p : ℕ) [Fact p.Prime] (hR : IsIntegralPerfectoid R p)
    (β : A →ₐ[R] P) (hβ : IsPerfectoidization p β.toRingHom)
    (η : E →ₐ[R] Q) (hη : IsPerfectoidization p η.toRingHom)
    (d : R) (L : Type u) [CommRing L] [Algebra R L] [IsLocalization (.powers d) L]
    (r : ℕ) (e : L ⊗[R] A ≃ₐ[L] (Fin r → L))
    (a : A →ₐ[R] E) (b : (Fin r → R) →ₐ[R] E)
    (l : E →ₐ[R] (Fin r → L)) [IsLocalizedModule (.powers d) l.toLinearMap]
    (ha : ∀ x, l (a x) = e ((1 : L) ⊗ₜ[R] x))
    (hb : ∀ z i, l (b z) i = algebraMap R L (z i))
    (hfree : IsIntegralPerfectoid (Fin r → R) p)
    (hPBa : BhattScholze.KLCanonicalExcisionSquare hβ hη a d)
    (hPBb : BhattScholze.KLCanonicalExcisionSquare (f := AlgHom.id R (Fin r → R))
      hfree.isPerfectoidization_id
      hη b d) :
    ∃ q : ℕ, moduleMapConeScalar R β.toLinearMap (d ^ q) = 0 := by
  letI := hR.isReduced R p
  let h := AlgHom.id R (Fin r → R)
  have hh : IsPerfectoidization p h.toRingHom :=
    hfree.isPerfectoidization_id
  have hd : d ∈ _root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal R p hR d :=
    _root_.SerrePositivity.BhattScholze.Almost.span_le_perfectoidIdeal R p hR d (Ideal.subset_span (Set.mem_singleton d))
  obtain ⟨hak, _hac⟩ :=
    BhattScholze.perfectoidization_comparison_almost_of_canonical_excision hR hβ hη a d hPBa
  obtain ⟨hbk, hbc⟩ :=
    BhattScholze.perfectoidization_comparison_almost_of_canonical_excision hR hh hη b d hPBb
  have heq : IsPerfectoidization.mapAlgHom hh hη b = η.comp b := by
    simpa only [h, AlgHom.comp_id] using IsPerfectoidization.mapAlgHom_comp hh hη b
  rw [heq] at hbk hbc
  apply fixed_cone_of_localized_splitting p β hβ η hη d L r e a b l ha hb
  · intro y hy
    exact congrArg Subtype.val (hak d hd ⟨y, hy⟩)
  · intro z hz
    exact congrArg Subtype.val (hbk d hd ⟨z, hz⟩)
  · exact hbc d hd

end SerrePositivity.CLMST

end Prop247ExcisionLocalPart

section Prop247ConstantRankExcisionPart

namespace SerrePositivity.CLMST
open _root_.SerrePositivity.BhattScholze
open scoped _root_.TensorProduct
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- 定 rank の元の指定写像について、実有限被覆と KL の指定 excision 入力から錐零化を得る。
被覆ごとの比較を使い、大域的な一つの自由比較は仮定しない。
rank の値は被覆構成に不要だが、原典の定 rank 段階の入口として明示する。 -/
theorem aic_constantRank_isogeny_of_finiteComparison_excision
    {R A P : Type u} [CommRing R] [CommRing A] [CommRing P]
    [Algebra R A] [Algebra R P] [Module.Finite R A] [Algebra.FinitePresentation R A]
    (p : ℕ) [Fact p.Prime] (hR : IsIntegralPerfectoid R p)
    (hAIC : IsAbsolutelyIntegrallyClosed R) (hExcision : BhattScholze.KLFiniteComparisonExcision R p)
    (g : R) (β : A →ₐ[R] P) (hβ : IsPerfectoidization p β.toRingHom)
    (hetale : letI := GenericEtale.awayAlgebra R A g
      Algebra.Etale (Localization.Away g) (Localization.Away (algebraMap R A g)))
    (r₀ : ℕ) (_hRank : ∀ x : PrimeSpectrum.basicOpen g, awayRank R A g x = r₀) :
    ∃ q : ℕ, moduleMapConeScalar R β.toLinearMap (g ^ q) = 0 := by
  classical
  obtain ⟨t, _ht, hcover, hmodels⟩ :=
    aic_finiteEtaleAway_exists_derivedComplete_common_cover p hR hAIC g hetale
  let U : Finset R := t.attach.image (fun z : t => g * (IsLocalization.Away.sec g z.1).1)
  have hU : (U : Set R) = Set.range (fun z : t => g * (IsLocalization.Away.sec g z.1).1) := by
    simp only [U, Finset.coe_image, Finset.coe_attach, Set.image_univ]
  apply moduleMapConeScalar_of_finite_cover β.toLinearMap g U
  · simpa only [hU] using hcover
  · intro d hd
    obtain ⟨z, _hz, rfl⟩ := Finset.mem_image.mp hd
    obtain ⟨r, e, E, hE, aE, hfinite, hfp, _hmfp, _hcR, _hcE, _hcI, _hcQ,
      a, b, l, ha, hb, hloc, haF, hbF, _hta, _htb, hak, hbk, n, hac, hbc⟩ :=
      hmodels z.1 z.2
    letI := hE
    letI := aE
    letI : Module.Finite R E := hfinite
    letI : Algebra.FinitePresentation R E := hfp
    obtain ⟨Q, hQ, η₀, hη₀⟩ :=
      BhattScholze.Inputs.exists_perfectoidization_of_integral R E p hR
    letI := hQ
    letI : Algebra R Q := (η₀.comp (algebraMap R E)).toAlgebra
    let η : E →ₐ[R] Q := { η₀ with commutes' := fun _ => rfl }
    have hη : IsPerfectoidization p η.toRingHom := hη₀
    let d := g * (IsLocalization.Away.sec g z.1).1
    letI : IsLocalization (.powers d) (Localization.Away z.1) :=
      principalLocalizationTower_isLocalization g z.1
    letI : IsLocalizedModule (.powers d) l.toLinearMap := hloc
    let e' := (doubleLocalizationTensorEquiv R A g z.1).trans e
    have ha' (x : A) : l (a x) = e' ((1 : Localization.Away z.1) ⊗ₜ[R] x) := by
      change l (a x) = e (doubleLocalizationTensorEquiv R A g z.1
        ((1 : Localization.Away z.1) ⊗ₜ[R] x))
      rw [doubleLocalizationTensorEquiv_tmul]
      exact ha x
    have hfree := isIntegralPerfectoid_finPi R p hR r
    let h := AlgHom.id R (Fin r → R)
    have hh : IsPerfectoidization p h.toRingHom := hfree.isPerfectoidization_id
    exact fixed_cone_of_two_canonical_excision p hR β hβ η hη
      d (Localization.Away z.1) r e' a b l ha' hb hfree
      (hExcision A E P Q d a haF hak ⟨n, hac⟩ β η hβ hη)
      (hExcision (Fin r → R) E (Fin r → R) Q d b hbF hbk ⟨n, hbc⟩ h η hh hη)

end SerrePositivity.CLMST

end Prop247ConstantRankExcisionPart
