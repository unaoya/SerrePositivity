module

public import SerrePositivity.BhattScholze.Andre.RootedExtension.DeltaRoot.DeltaRootRelationKoszul
public import SerrePositivity.BhattScholze.Andre.RootedExtension.MonicPowerFamilyBaseQuotient
public import Mathlib.Algebra.MvPolynomial.Equiv

/-! # 先行する根関係で割った商の具体的な多項式表示

添字を残りの変数τと先行変数ιの直和として表示する。
根添加済み係数環は既存MonicPowerFamilyCoverを使用する。
-/

@[expose] public noncomputable section
universe u v w
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} {A : Type u} [CommRing A] {τ : Type v} {ι : Type w}
variable (b : τ ⊕ ι → A)

/-- 先行変数のみの根関係を課すイデアル。 -/
def deltaRootPartialRelationIdeal : Ideal (MvPolynomial (τ ⊕ ι) A) :=
  Ideal.span (Set.range fun s : ι ↦ deltaRootRelationFamily (p := p) b (Sum.inr s))

/-- 添字分割同型は先行根関係を係数側の関係式イデアルへ送る。 -/
theorem deltaRootPartialRelationIdeal_map_sum :
    (deltaRootPartialRelationIdeal (p := p) b).map
      (MvPolynomial.sumRingEquiv A τ ι).toRingHom =
    (monicPowerFamilyRelationIdeal p ι A (fun s ↦ b (Sum.inr s))).map
      (MvPolynomial.C : MvPolynomial ι A →+* MvPolynomial τ (MvPolynomial ι A)) := by
  simp only [deltaRootPartialRelationIdeal, monicPowerFamilyRelationIdeal, Ideal.map_span,
    ← Set.range_comp', deltaRootRelationFamily, map_sub, map_pow,
    RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
    MvPolynomial.sumRingEquiv_X_inr, MvPolynomial.sumRingEquiv_C]

/-- 先行関係式の商は、既存根添加環を係数環とする残りの変数の多項式環。 -/
def deltaRootPartialQuotientEquiv :
    (MvPolynomial (τ ⊕ ι) A ⧸ deltaRootPartialRelationIdeal (p := p) b) ≃+*
      MvPolynomial τ (MonicPowerFamilyCover p ι A (fun s ↦ b (Sum.inr s))) :=
  ((Ideal.quotientEquiv _ _ (MvPolynomial.sumRingEquiv A τ ι)
    (deltaRootPartialRelationIdeal_map_sum b).symm).trans
    (MvPolynomial.quotientEquivQuotientMvPolynomial
      (σ := τ)
      (monicPowerFamilyRelationIdeal p ι A (fun s ↦ b (Sum.inr s)))).symm.toRingEquiv).trans
    (MvPolynomial.mapEquiv τ
      (monicPowerFamilyPresentationEquiv p ι A (fun s ↦ b (Sum.inr s))))

/-- 商同型の標準商射上の具体的な式。 -/
theorem deltaRootPartialQuotientEquiv_mk (x : MvPolynomial (τ ⊕ ι) A) :
    deltaRootPartialQuotientEquiv (p := p) b (Ideal.Quotient.mk _ x) =
      MvPolynomial.map (monicPowerFamilyQuotientMap p ι A (fun s ↦ b (Sum.inr s)))
        (MvPolynomial.map (Ideal.Quotient.mk _) (MvPolynomial.sumRingEquiv A τ ι x)) := by
  change MvPolynomial.map _
    ((MvPolynomial.quotientEquivQuotientMvPolynomial (σ := τ) _).symm
      (Ideal.Quotient.mk _ (MvPolynomial.sumRingEquiv A τ ι x))) = _
  rw [← monicPowerFamilyCoefficientQuotient_comp]
  rfl

/-- 元の係数は根添加済み係数環の標準係数像へ送られる。 -/
theorem deltaRootPartialQuotientEquiv_C (a : A) :
    deltaRootPartialQuotientEquiv (p := p) b (Ideal.Quotient.mk _ (MvPolynomial.C a)) =
      MvPolynomial.C (algebraMap A (MonicPowerFamilyCover p ι A (fun s ↦ b (Sum.inr s))) a) := by
  rw [deltaRootPartialQuotientEquiv_mk, MvPolynomial.sumRingEquiv_C,
    MvPolynomial.map_C, MvPolynomial.map_C]
  exact congrArg MvPolynomial.C (monicPowerFamilyPresentationEquiv_coeff p ι A _ a)

/-- 残りの変数はそのまま多項式変数に対応する。 -/
theorem deltaRootPartialQuotientEquiv_X_inl (s : τ) :
    deltaRootPartialQuotientEquiv (p := p) b (Ideal.Quotient.mk _ (MvPolynomial.X (Sum.inl s))) =
      MvPolynomial.X s := by
  rw [deltaRootPartialQuotientEquiv_mk, MvPolynomial.sumRingEquiv_X_inl,
    MvPolynomial.map_X, MvPolynomial.map_X]

/-- 先行変数は既存の指定根に対応する。 -/
theorem deltaRootPartialQuotientEquiv_X_inr (s : ι) :
    deltaRootPartialQuotientEquiv (p := p) b (Ideal.Quotient.mk _ (MvPolynomial.X (Sum.inr s))) =
      MvPolynomial.C (monicPowerFamilyRoot p ι A (fun t ↦ b (Sum.inr t)) s) := by
  rw [deltaRootPartialQuotientEquiv_mk, MvPolynomial.sumRingEquiv_X_inr,
    MvPolynomial.map_C, MvPolynomial.map_C]
  exact congrArg MvPolynomial.C (monicPowerFamilyPresentationEquiv_root p ι A _ s)

/-- 先行する根関係で割った後も、残りの各根関係は非零因子。 -/
theorem deltaRootPartialQuotient_remaining_isSMulRegular [Fact p.Prime] (s : τ) :
    IsSMulRegular (MvPolynomial (τ ⊕ ι) A ⧸ deltaRootPartialRelationIdeal (p := p) b)
      (Ideal.Quotient.mk (deltaRootPartialRelationIdeal (p := p) b)
        (deltaRootRelationFamily (p := p) b (Sum.inl s))) := by
  let e := deltaRootPartialQuotientEquiv (p := p) b
  have he : e (Ideal.Quotient.mk (deltaRootPartialRelationIdeal (p := p) b)
      (deltaRootRelationFamily (p := p) b (Sum.inl s))) =
      deltaRootRelationFamily (p := p)
        (fun t : τ ↦ algebraMap A (MonicPowerFamilyCover p ι A
          (fun r ↦ b (Sum.inr r))) (b (Sum.inl t))) s := by
    simp only [deltaRootRelationFamily, map_sub, map_pow, e,
      deltaRootPartialQuotientEquiv_X_inl, deltaRootPartialQuotientEquiv_C]
  have h := deltaRootRelation_isSMulRegular (p := p)
    (fun t : τ ↦ algebraMap A (MonicPowerFamilyCover p ι A
      (fun r ↦ b (Sum.inr r))) (b (Sum.inl t))) s
  intro x y hxy
  apply e.injective
  apply h
  have hh := congrArg e hxy
  simpa only [smul_eq_mul, map_mul, he] using hh

/-- 先行関係式の商上でも、後続一関係のKoszul複体は実際の商の分解となる。 -/
theorem deltaRootPartialQuotient_remaining_isKoszulResolution [Fact p.Prime] (s : τ) :
    SerrePositivity.IsKoszulResolution (fun _ : Fin 1 ↦
      (Ideal.Quotient.mk (deltaRootPartialRelationIdeal (p := p) b)
        (deltaRootRelationFamily (p := p) b (Sum.inl s)))) := by
  apply SerrePositivity.isKoszulResolution_of_isWeaklyRegular
  rw [List.ofFn_const, List.replicate_one,
    RingTheory.Sequence.isWeaklyRegular_singleton_iff]
  exact deltaRootPartialQuotient_remaining_isSMulRegular b s

end SerrePositivity.BhattScholze
