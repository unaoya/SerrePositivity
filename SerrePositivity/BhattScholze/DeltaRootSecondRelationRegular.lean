module

public import SerrePositivity.BhattScholze.DeltaDivisionFiniteRelationsRegular
public import SerrePositivity.BhattScholze.DeltaRootFirstEvaluationQuotient
public import SerrePositivity.BhattScholze.OrientedPrism

/-! # 一般d根添加の深さ1関係の非零因子性

深さ0商の元の係数環上の忠実平坦性を使い、φ(d)の正則性を供給する。
異なる複数の深さ1関係の列や、全深さの正則性はここでは結論しない。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (D : DeltaStructure p A) (d : A) (b : σ → A)
local notation "P₀" => MvPolynomial σ A
local notation "L₀" => RelativeFreeDeltaRing (R := P₀) σ
local notation "E₀" => polynomialRankOneDeltaStructure σ D
local notation "c₀" => deltaRootRelationFamily (p := p) b
local notation "I₀" => deltaDivisionFiniteRelationIdeal E₀ (MvPolynomial.C d) c₀

/-- φ(d)が元の係数環上で正則なら、実段0商上の次関係の先頭係数も正則。 -/
theorem deltaRootFirstQuotient_frobenius_coefficient_isSMulRegular
    (hd : IsSMulRegular A (D.frobeniusLift d)) :
    IsSMulRegular (L₀ ⧸ I₀ 0)
      (Ideal.Quotient.mk (I₀ 0) (MvPolynomial.C ((E₀).frobeniusLift (MvPolynomial.C d)))) := by
  let := deltaRootFirstEvaluationQuotient_base_moduleFaithfullyFlat D d b
  have hr := hd.of_flat (S := DeltaRootFirstEvaluationQuotient D d b)
  have hφ : (E₀).frobeniusLift (MvPolynomial.C d) = MvPolynomial.C (D.frobeniusLift d) := by
    simp only [DeltaStructure.frobeniusLift_apply, polynomialRankOneDeltaStructure_delta_C,
      map_add, map_pow, map_mul, map_natCast]
  rw [← deltaRootFirstEvaluationIdeal_eq_finiteRelationIdeal D d b, hφ]
  exact hr

/-- 任意の根添字について、深さ1の実δ関係は全深さ0商上の非零因子。 -/
theorem deltaRootSecondRelation_isSMulRegular (s : σ)
    (hd : IsSMulRegular A (D.frobeniusLift d)) :
    IsSMulRegular (L₀ ⧸ I₀ 0)
      (Ideal.Quotient.mk (I₀ 0)
        (deltaDivisionIteratedRelation E₀ (MvPolynomial.C d) c₀ s 1)) := by
  apply deltaDivisionFiniteStage_next_isSMulRegular_of_frobenius_regular
  exact deltaRootFirstQuotient_frobenius_coefficient_isSMulRegular D d b hd

/-- 完全δ環では、dの正則性から深さ1の非零因子性を得る。 -/
theorem deltaRootSecondRelation_isSMulRegular_of_perfect (s : σ)
    (hD : D.IsPerfect) (hd : IsSMulRegular A d) :
    IsSMulRegular (L₀ ⧸ I₀ 0)
      (Ideal.Quotient.mk (I₀ 0)
        (deltaDivisionIteratedRelation E₀ (MvPolynomial.C d) c₀ s 1)) := by
  apply deltaRootSecondRelation_isSMulRegular D d b s
  apply (Equiv.isSMulRegular_congr
    (e := (RingEquiv.ofBijective D.frobeniusLift hD).toEquiv)
    (r := d) (s := D.frobeniusLift d) ?_).mp hd
  intro x
  change D.frobeniusLift (d * x) = D.frobeniusLift d * D.frobeniusLift x
  exact map_mul D.frobeniusLift d x

/-- 完全prismの指定生成元には、追加の係数正則性を仮定せずに深さ1判定を適用できる。 -/
theorem deltaRootSecondRelation_isSMulRegular_of_perfectPrism
    (P : OrientedPrism p A) (hP : P.deltaStructure.IsPerfect) (s : σ) :
    IsSMulRegular
      (RelativeFreeDeltaRing (R := MvPolynomial σ A) σ ⧸
        deltaDivisionFiniteRelationIdeal (polynomialRankOneDeltaStructure σ P.deltaStructure)
          (MvPolynomial.C P.generator) (deltaRootRelationFamily (p := p) b) 0)
      (Ideal.Quotient.mk
        (deltaDivisionFiniteRelationIdeal (polynomialRankOneDeltaStructure σ P.deltaStructure)
          (MvPolynomial.C P.generator) (deltaRootRelationFamily (p := p) b) 0)
        (deltaDivisionIteratedRelation (polynomialRankOneDeltaStructure σ P.deltaStructure)
          (MvPolynomial.C P.generator) (deltaRootRelationFamily (p := p) b) s 1)) :=
  deltaRootSecondRelation_isSMulRegular_of_perfect P.deltaStructure P.generator b s hP
    P.generator_regular

end SerrePositivity.BhattScholze
