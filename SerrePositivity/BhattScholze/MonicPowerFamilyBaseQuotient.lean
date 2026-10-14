module

public import SerrePositivity.BhattScholze.MonicPowerFamilyPresentation
public import Mathlib.RingTheory.Polynomial.Quotient

/-! # モニック冪根添加の係数商との比較

既存の係数商・二重商・モニック商表示の同型を合成する。
BSの有限δ剰余の表示へ適用するための比較。
-/

@[expose] public noncomputable section
universe u v
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable (n : ℕ) (σ : Type u) (R : Type v) [CommRing R]

/-- 既存係数商同型と標準商射の合成は係数の商写像である。 -/
theorem monicPowerFamilyCoefficientQuotient_comp (I : Ideal R) :
    (MvPolynomial.quotientEquivQuotientMvPolynomial (σ := σ) I).symm.toRingHom.comp
      (Ideal.Quotient.mk (I.map (MvPolynomial.C : R →+* MvPolynomial σ R))) =
      MvPolynomial.map (Ideal.Quotient.mk I) := by
  apply RingHom.ext
  intro x
  change MvPolynomial.eval₂Hom (MvPolynomial.C.comp (Ideal.Quotient.mk I)) MvPolynomial.X x = _
  rw [MvPolynomial.map_eq_eval₂Hom_C_comp]

/-- モニック関係式は係数の商と既存係数商同型で、剰余係数の関係式へ移る。 -/
theorem monicPowerFamilyRelationIdeal_map_coefficientQuotient (I : Ideal R) (c : σ → R) :
    ((monicPowerFamilyRelationIdeal n σ R c).map
      (Ideal.Quotient.mk (I.map (MvPolynomial.C : R →+* MvPolynomial σ R)))).map
      (MvPolynomial.quotientEquivQuotientMvPolynomial (σ := σ) I).symm.toRingHom =
      monicPowerFamilyRelationIdeal n σ (R ⧸ I) (fun s => Ideal.Quotient.mk I (c s)) := by
  rw [Ideal.map_map, monicPowerFamilyCoefficientQuotient_comp]
  simp only [monicPowerFamilyRelationIdeal, Ideal.map_span, ← Set.range_comp', map_sub, map_pow,
    MvPolynomial.map_X, MvPolynomial.map_C]

/-- 係数イデアルとモニック冪関係式による商は、係数商上の通常根添加環。 -/
def monicPowerFamilyBaseQuotientEquiv (I : Ideal R) (c : σ → R) :
    (MvPolynomial σ R ⧸ (I.map (MvPolynomial.C : R →+* MvPolynomial σ R) ⊔
      monicPowerFamilyRelationIdeal n σ R c)) ≃+*
      MonicPowerFamilyCover n σ (R ⧸ I) (fun s => Ideal.Quotient.mk I (c s)) :=
  ((DoubleQuot.quotQuotEquivQuotSup
    (I.map (MvPolynomial.C : R →+* MvPolynomial σ R))
    (monicPowerFamilyRelationIdeal n σ R c)).symm.trans
    (Ideal.quotientEquiv _ _
      (MvPolynomial.quotientEquivQuotientMvPolynomial (σ := σ) I).symm.toRingEquiv
      (monicPowerFamilyRelationIdeal_map_coefficientQuotient n σ R I c).symm)).trans
    (monicPowerFamilyPresentationEquiv n σ (R ⧸ I) (fun s => Ideal.Quotient.mk I (c s)))

/-- 係数商比較同型は標準商射上で既存モニック商射と一致する。 -/
theorem monicPowerFamilyBaseQuotientEquiv_mk (I : Ideal R) (c : σ → R)
    (x : MvPolynomial σ R) :
    monicPowerFamilyBaseQuotientEquiv n σ R I c
      (Ideal.Quotient.mk (I.map MvPolynomial.C ⊔ monicPowerFamilyRelationIdeal n σ R c) x) =
      monicPowerFamilyQuotientMap n σ (R ⧸ I) (fun s => Ideal.Quotient.mk I (c s))
        (Ideal.Quotient.mk _ (MvPolynomial.map (Ideal.Quotient.mk I) x)) := by
  change monicPowerFamilyQuotientMap n σ (R ⧸ I) (fun s => Ideal.Quotient.mk I (c s))
    (Ideal.Quotient.mk _ (MvPolynomial.eval₂Hom
      (MvPolynomial.C.comp (Ideal.Quotient.mk I)) MvPolynomial.X x)) = _
  rw [MvPolynomial.map_eq_eval₂Hom_C_comp]

/-- 係数商比較同型は元の係数を標準係数射の像へ送る。 -/
@[simp] theorem monicPowerFamilyBaseQuotientEquiv_C (I : Ideal R) (c : σ → R) (r : R) :
    monicPowerFamilyBaseQuotientEquiv n σ R I c
      (Ideal.Quotient.mk _ (MvPolynomial.C r)) =
      algebraMap (R ⧸ I) (MonicPowerFamilyCover n σ (R ⧸ I)
        (fun s => Ideal.Quotient.mk I (c s))) (Ideal.Quotient.mk I r) := by
  rw [monicPowerFamilyBaseQuotientEquiv_mk, MvPolynomial.map_C]
  change monicPowerFamilyEvaluation n σ (R ⧸ I) _ (MvPolynomial.C _) = _
  simp [monicPowerFamilyEvaluation]

/-- 係数商比較同型は変数を指定根へ送る。 -/
@[simp] theorem monicPowerFamilyBaseQuotientEquiv_X (I : Ideal R) (c : σ → R) (s : σ) :
    monicPowerFamilyBaseQuotientEquiv n σ R I c (Ideal.Quotient.mk _ (MvPolynomial.X s)) =
      monicPowerFamilyRoot n σ (R ⧸ I) (fun t => Ideal.Quotient.mk I (c t)) s := by
  rw [monicPowerFamilyBaseQuotientEquiv_mk, MvPolynomial.map_X]
  change monicPowerFamilyEvaluation n σ (R ⧸ I) _ (MvPolynomial.X s) = _
  simp [monicPowerFamilyEvaluation]

end SerrePositivity.BhattScholze
