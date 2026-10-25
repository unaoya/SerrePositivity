module

public import SerrePositivity.BhattScholze.Delta.DeltaTorsion
public import Mathlib.FieldTheory.Perfect

/-! # 完全δ環のmod pの完全性

BS著者公開版Corollary 2.31の(1)から(2)の代数的部分。
φが全単射ならA/(p)のp乗写像も全単射である。完備性はこの部分には不要。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.BhattScholze.DeltaStructure
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]

/-- 完全δ構造のmod p商は完全環。φがpを固定するので、φによる(p)の逆像も(p)。
零環を含み、古典的・導来完備性はいずれも仮定しない（BS Cor 2.31の一方向）。 -/
theorem IsPerfect.perfectRing_mod_p {D : DeltaStructure p A} (hD : D.IsPerfect) :
    PerfectRing (A ⧸ Ideal.span {(p : A)}) p := by
  let I := Ideal.span {(p : A)}
  let q := Ideal.Quotient.mk I
  have hqp : q (p : A) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))
  have hmod (x : A) : q (D.frobeniusLift x) = q x ^ p :=
    D.map_frobeniusLift_of_map_p_eq_zero q hqp x
  refine ⟨⟨?_, ?_⟩⟩
  · intro x y hxy
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
    change q a ^ p = q b ^ p at hxy
    have hz : q (D.frobeniusLift (a - b)) = 0 := by
      rw [map_sub, map_sub, hmod a, hmod b, hxy, sub_self]
    obtain ⟨r, hr⟩ := Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp hz)
    obtain ⟨s, hs⟩ := hD.2 r
    have he : a - b = (p : A) * s := by
      apply hD.1
      rw [map_mul, map_natCast, hs]
      exact hr
    apply Ideal.Quotient.eq.mpr
    exact Ideal.mem_span_singleton.mpr ⟨s, he⟩
  · intro x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨b, hb⟩ := hD.2 a
    exact ⟨q b, (hmod b).symm.trans (congrArg q hb)⟩

end SerrePositivity.BhattScholze.DeltaStructure
