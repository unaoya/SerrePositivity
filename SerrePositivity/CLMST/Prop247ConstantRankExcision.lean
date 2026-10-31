module

public import SerrePositivity.CLMST.Prop247ExcisionLocal
public import SerrePositivity.CLMST.Prop247RankLoci
public import SerrePositivity.HomologicalAlgebra.ScalarConeAnnihilators

/-! # Prop 2.4.7：定 rank の実被覆からの条件付き組立て

元の A と指定 perfectoid 化を固定し、実被覆と共通モデルを構成する。
未供給入力は KL の指定 canonical excision 四角形の引き戻し性である。
共通モデルと有限自由環の perfectoid 化には既存の一般 integral 存在 B-I が残る。
新しい引用・sorry・axiom は追加しない。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.CLMST
open BhattScholze
open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- 定 rank の元の指定写像について、実有限被覆と KL の指定 excision 入力から錐零化を得る。
被覆ごとの比較を使い、大域的な一つの自由比較は仮定しない。
rank の値は被覆構成に不要だが、原典の定 rank 段階の入口として明示する。 -/
theorem prop247_aic_constantRank_isogeny_of_finiteComparison_excision
    {R A P : Type u} [CommRing R] [CommRing A] [CommRing P]
    [Algebra R A] [Algebra R P] [Module.Finite R A] [Algebra.FinitePresentation R A]
    (p : ℕ) [Fact p.Prime] (hR : IsIntegralPerfectoid R p)
    (hAIC : IsAbsolutelyIntegrallyClosed R) (hExcision : KLFiniteComparisonExcision R p)
    (g : R) (β : A →ₐ[R] P) (hβ : IsPerfectoidization p β.toRingHom)
    (hetale : letI := GenericEtale.awayAlgebra R A g
      Algebra.Etale (Localization.Away g) (Localization.Away (algebraMap R A g)))
    (r₀ : ℕ) (_hRank : ∀ x : PrimeSpectrum.basicOpen g, prop247_awayRank R A g x = r₀) :
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
    exact prop247_fixed_cone_of_two_canonical_excision p hR β hβ η hη
      d (Localization.Away z.1) r e' a b l ha' hb hfree
      (hExcision A E P Q d a haF hak ⟨n, hac⟩ β η hβ hη)
      (hExcision (Fin r → R) E (Fin r → R) Q d b hbF hbk ⟨n, hbc⟩ h η hh hη)

end SerrePositivity.CLMST
