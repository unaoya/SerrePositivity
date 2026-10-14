module

public import SerrePositivity.BhattScholze.PerfectDeltaFrobenius

/-! # 完全δ環の商におけるmod p Frobenius全射性

著者公開版Theorem 3.10の逆向きの最初の計算。
完備性やFontaine核の単項性を仮定せず、perfectoid性全体は結論しない。
-/

@[expose] public noncomputable section
universe u v
namespace SerrePositivity.BhattScholze.DeltaStructure
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]

/-- 完全δ環からpを零に送る全射環射の終域では、p乗写像が全射。 -/
theorem IsPerfect.surjective_pow_of_surjective_map_p_eq_zero
    {D : DeltaStructure p A} (hD : D.IsPerfect) {B : Type v} [CommRing B]
    (q : A →+* B) (hq : Function.Surjective q) (hp : q (p : A) = 0) :
    Function.Surjective (fun x : B ↦ x ^ p) := by
  intro y
  obtain ⟨a, rfl⟩ := hq y
  obtain ⟨b, hb⟩ := hD.2 a
  refine ⟨q b, ?_⟩
  change (q b) ^ p = q a
  rw [← D.map_frobeniusLift_of_map_p_eq_zero q hp, hb]

/-- 完全δ環の任意のイデアル商はmod pでFrobenius全射。
一般の商を扱い、pねじれのない商に限定しない。 -/
theorem IsPerfect.quotient_mod_p_frobenius_surjective {D : DeltaStructure p A}
    (hD : D.IsPerfect) (I : Ideal A) :
    Function.Surjective (fun x : (A ⧸ I) ⧸ Ideal.span {(p : A ⧸ I)} ↦ x ^ p) := by
  let q := (Ideal.Quotient.mk (Ideal.span {(p : A ⧸ I)})).comp (Ideal.Quotient.mk I)
  apply hD.surjective_pow_of_surjective_map_p_eq_zero q
    (Ideal.Quotient.mk_surjective.comp Ideal.Quotient.mk_surjective)
  change Ideal.Quotient.mk (Ideal.span {(p : A ⧸ I)}) (Ideal.Quotient.mk I (p : A)) = 0
  rw [map_natCast]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))

end SerrePositivity.BhattScholze.DeltaStructure
