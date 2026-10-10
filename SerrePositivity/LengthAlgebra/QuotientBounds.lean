module

public import SerrePositivity.LengthAlgebra.Koszul

/-! # パラメータ商のさらに大きな商の長さ

下界で使う `C/Q` の有限性と冪ねじれ性を、既存の支持条件と Koszul 有限性から得る。
`C` の Noether 性は使わず、第零 Koszul ホモロジーと商への全射を用いる。
-/

@[expose] public section

universe u

namespace SerrePositivity.LengthAlgebra

open scoped ENNReal

variable {C : Type u} [CommRing C] {J : Ideal C}
  (lam : NormalizedLength C J) (hfg : J.FG) {e : ℕ} (z : Fin e → C)
  (hJ : J ≤ (Ideal.span (Set.range z)).radical) (Q : Ideal C)
  (hzQ : Ideal.span (Set.range z) ≤ Q)

include hfg hJ hzQ in
/-- パラメータを消す商は、長さの定義域である冪ねじれ条件を満たす。 -/
lemma quotient_isPowTorsion_of_span_le : IsPowTorsion J (C ⧸ Q) := by
  apply IsPowTorsion.of_le_radical_annihilator hfg
  rw [Ideal.annihilator_quotient]
  exact hJ.trans (Ideal.radical_mono hzQ)

include hfg hJ hzQ in
/-- パラメータ商からの全射により、下界に使う商の長さも制御できる。 -/
lemma length_quotient_le_of_span_le :
    lam.len (C ⧸ Q) ≤ lam.len (C ⧸ Ideal.span (Set.range z)) := by
  apply lam.len_le_of_surjective (Ideal.Quotient.factorₐ C hzQ).toLinearMap
    (Ideal.Quotient.factor_surjective hzQ)
  exact quotient_isPowTorsion_of_span_le hfg z hJ _ le_rfl

include hfg hJ hzQ in
/-- Koszul 有限性は、パラメータを消す任意の商の長さの有限性を含意する。 -/
lemma length_quotient_ne_top_of_koszul_finite (hfin : KoszulFinite lam z) :
    lam.len (C ⧸ Q) ≠ ⊤ := by
  have hzero : lam.len ((koszulComplex z).homology 0) ≠ ⊤ := by
    have hz : (fun j ↦ z j ^ 1) = z := funext fun j ↦ pow_one (z j)
    exact (congrArg (fun w ↦ lam.len ((koszulComplex w).homology (0 : ℤ)) ≠ ⊤) hz).mp
      (hfin 1 one_pos 0)
  have hquot : lam.len (C ⧸ Ideal.span (Set.range z)) ≠ ⊤ := by
    rwa [lam.len_congr _ _ (koszulComplex_homology_zero_equiv z).some] at hzero
  exact ne_top_of_le_ne_top hquot (length_quotient_le_of_span_le lam hfg z hJ Q hzQ)

end SerrePositivity.LengthAlgebra
