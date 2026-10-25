module

public import SerrePositivity.BhattScholze.Delta.Basic.DeltaQuotient
public import Mathlib.RingTheory.WittVector.Identities
public import Mathlib.RingTheory.Jacobson.Ideal

/-! # δ(p)のmod p計算

W₂切断の自然数上の値とMathlibの標数pにおけるWitt係数を用いる。
BS著者版Example 2.20(1)の単元性に必要な合同式を、p正則性なしで証明する。
-/

@[expose] public noncomputable section
universe u v
namespace SerrePositivity.BhattScholze.DeltaStructure
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]

/-- 標数pの環への任意の環準同型はδ(p)を1に送る。
δ射である必要はなく、W₂切断が自然数を保存することから従う。 -/
theorem map_delta_p {B : Type v} [CommRing B] [CharP B p]
    (D : DeltaStructure p A) (f : A →+* B) : f (D.delta (p : A)) = 1 := by
  have h := wittTwoMap_coeff (p := p) f (D.sectionHom (p : A)) (1 : Fin 2)
  simp only [map_natCast] at h
  change (p : WittVector p B).coeff 1 = f ((p : WittVector p A).coeff 1) at h
  rw [WittVector.coeff_p_one] at h
  change f ((D.sectionHom (p : A)).coeff 1) = 1
  rw [map_natCast]
  exact h.symm

/-- δ(p)はmod pで1に一致する。零環・pねじれを持つ環も含む。 -/
theorem delta_p_sub_one_mem (D : DeltaStructure p A) :
    D.delta (p : A) - 1 ∈ Ideal.span {(p : A)} := by
  let I := Ideal.span {(p : A)}
  let q := Ideal.Quotient.mk I
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  rcases subsingleton_or_nontrivial (A ⧸ I) with hsub | hnontrivial
  · let := hsub
    exact Subsingleton.elim _ _
  · let := hnontrivial
    have hp0 : (p : A ⧸ I) = 0 := by
      rw [← map_natCast q]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))
    let : CharP (A ⧸ I) p := (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).mpr hp0
    change q (D.delta (p : A) - 1) = 0
    rw [map_sub, D.map_delta_p q, map_one, sub_self]

/-- pがJacobson根基に属するδ環ではpがdistinguished。
δ(p)-1が(p)に属する合同式とJacobson根基の単元判定を使う。 -/
theorem isDistinguished_p (D : DeltaStructure p A)
    (hpr : (p : A) ∈ Ideal.jacobson (⊥ : Ideal A)) : D.IsDistinguished (p : A) := by
  apply Ideal.isUnit_of_sub_one_mem_jacobson_bot
  have hle : Ideal.span {(p : A)} ≤ Ideal.jacobson (⊥ : Ideal A) :=
    Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hpr)
  exact hle D.delta_p_sub_one_mem

end SerrePositivity.BhattScholze.DeltaStructure
