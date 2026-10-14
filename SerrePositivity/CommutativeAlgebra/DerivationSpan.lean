module

public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.RingTheory.Kaehler.Basic

/-! # 代数の生成元と導分の像の線形包

導分の像の生成性を、代数の生成元上の像へ制限する。
有限生成性は一般定理に要求しない。
-/

@[expose] public section
namespace SerrePositivity

/-- 代数の生成元の導分の像は、全導分の像と同じ部分加群を生成する。 -/
theorem span_range_derivation_eq_span_of_adjoin_eq_top
    {R S V : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup V] [Module S V] [Module R V]
    (δ : Derivation R S V) (s : Set S) (hs : Algebra.adjoin R s = ⊤) :
    Submodule.span S (Set.range δ) = Submodule.span S (δ '' s) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨x, rfl⟩
    have hx : x ∈ Algebra.adjoin R s := hs.symm ▸ Algebra.mem_top
    induction hx using Algebra.adjoin_induction with
    | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
    | algebraMap r => simp
    | add x y _ _ hx hy => simpa using (Submodule.span S (δ '' s)).add_mem hx hy
    | mul x y _ _ hx hy =>
      rw [δ.leibniz]
      exact (Submodule.span S (δ '' s)).add_mem
        (Submodule.smul_mem _ _ hy) (Submodule.smul_mem _ _ hx)
  · exact Submodule.span_mono (Set.image_subset_range _ _)

/-- 通常の Kähler 微分は代数の生成元の微分で生成される。 -/
theorem span_kaehlerDifferential_of_adjoin_eq_top
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (s : Set S) (hs : Algebra.adjoin R s = ⊤) :
    Submodule.span S (KaehlerDifferential.D R S '' s) = ⊤ := by
  rw [← span_range_derivation_eq_span_of_adjoin_eq_top (KaehlerDifferential.D R S) s hs]
  exact KaehlerDifferential.span_range_derivation R S

/-- 標数 p の代数への導分は p 乗を消す。 -/
theorem derivation_pow_char_eq_zero
    {R S V : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup V] [Module S V] [Module R V]
    (p : ℕ) [CharP S p] (δ : Derivation R S V) (x : S) : δ (x ^ p) = 0 := by
  rw [δ.leibniz_pow, ← Nat.cast_smul_eq_nsmul S, CharP.cast_eq_zero S p, zero_smul]

end SerrePositivity
