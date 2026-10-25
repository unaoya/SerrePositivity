module

public import SerrePositivity.BhattScholze.Prism.PCompletedDeltaDivision
public import SerrePositivity.BhattScholze.Delta.DistinguishedPowerTorsion

/-! # 具体的なp進完備δ除算候補の生成元冪商の有界ねじれ

原典Lemma 3.9に向け、distinguished像のn乗商の有界pねじれ条件を供給する。
商のp完備性や導来(p,d)完備化との比較は結論しない。
-/

@[expose] public noncomputable section
universe u v
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {R : Type u} [CommRing R] {σ : Type v}

/-- 具体的な候補のj(d)ⁿ商でp冪ねじれはpⁿで消える。
基底Rの完全性・完備性は要求せず、候補について既存証明から供給する。 -/
theorem pCompletedDeltaDivision_quotient_power_p_pow_torsion_killed_by_p_pow
    (D : DeltaStructure p R) (d : R) (hd : D.IsDistinguished d) (a : σ → R) (n N : ℕ)
    (x : PCompletedDeltaDivision D d a ⧸ Ideal.span {(pCompletedDeltaDivisionMap D d a d) ^ n})
    (hx : (p : PCompletedDeltaDivision D d a ⧸
      Ideal.span {(pCompletedDeltaDivisionMap D d a d) ^ n}) ^ N * x = 0) :
    (p : PCompletedDeltaDivision D d a ⧸
      Ideal.span {(pCompletedDeltaDivisionMap D d a d) ^ n}) ^ n * x = 0 := by
  let := pCompletedDeltaDivision_isAdicComplete D d a
  have hC := pCompletedDeltaDivision_isPerfect D d a
  exact hC.distinguished_quotient_power_p_pow_torsion_killed_by_p_pow
      ((pCompletedDeltaDivisionMap_isDeltaHom D d a).map_isDistinguished hd) n N x hx

end SerrePositivity.BhattScholze
