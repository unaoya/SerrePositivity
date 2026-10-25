module

public import SerrePositivity.BhattScholze.Prism.Perfection.PCompletedDeltaPerfection
public import SerrePositivity.BhattScholze.Delta.Perfect.DistinguishedTorsion

/-! # p進完備なδ完全化の正則性とdistinguished商

具体的な完全化環と標準射に、既存Lemma 2.28・2.34の結果を適用する。
prismのイデアルの単項化や導来完備化との比較は結論しない。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]

/-- p進完備なδ完全化ではp倍が単射。 -/
theorem pCompletedDeltaPerfection_p_mul_injective (D : DeltaStructure p A) :
    Function.Injective (fun x : PCompletedDeltaPerfection D ↦
      (p : PCompletedDeltaPerfection D) * x) :=
  (pCompletedDeltaPerfection_isPerfect D).p_mul_injective

/-- 基底のdistinguished元の像はdistinguished。 -/
theorem pCompletedDeltaPerfectionMap_isDistinguished (D : DeltaStructure p A)
    {d : A} (hd : D.IsDistinguished d) :
    (pCompletedDeltaPerfectionStructure D).IsDistinguished (pCompletedDeltaPerfectionMap D d) :=
  (pCompletedDeltaPerfectionMap_isDeltaHom D).map_isDistinguished hd

/-- 基底のdistinguished元の像はp進完備なδ完全化で非零因子。 -/
theorem pCompletedDeltaPerfectionMap_mul_injective (D : DeltaStructure p A)
    {d : A} (hd : D.IsDistinguished d) :
    Function.Injective (fun x : PCompletedDeltaPerfection D ↦
      pCompletedDeltaPerfectionMap D d * x) := by
  let := pCompletedDeltaPerfection_isAdicComplete D
  exact (pCompletedDeltaPerfection_isPerfect D).distinguished_mul_injective
    (pCompletedDeltaPerfectionMap_isDistinguished D hd)

/-- distinguished元の標準像による商では、全てのp冪ねじれがpで消える。 -/
theorem pCompletedDeltaPerfection_quotient_p_pow_torsion_killed_by_p
    (D : DeltaStructure p A) {d : A} (hd : D.IsDistinguished d)
    (N : ℕ) (x : PCompletedDeltaPerfection D ⧸ Ideal.span {pCompletedDeltaPerfectionMap D d})
    (hx : (p : PCompletedDeltaPerfection D ⧸
      Ideal.span {pCompletedDeltaPerfectionMap D d}) ^ N * x = 0) :
    (p : PCompletedDeltaPerfection D ⧸ Ideal.span {pCompletedDeltaPerfectionMap D d}) * x = 0 :=
  (pCompletedDeltaPerfection_isPerfect D).distinguished_quotient_p_pow_torsion_killed_by_p
    (pCompletedDeltaPerfectionMap_isDistinguished D hd) N x hx

end SerrePositivity.BhattScholze
