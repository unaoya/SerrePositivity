module

public import Mathlib.RingTheory.Perfection

/-! # Frobeniusで根を取れる核を持つ全射のperfection

第0成分を指定してcompatibleな根の列を持ち上げる。
核内でp乗根を選び、隣接成分の誤差を除く。
-/

@[expose] public noncomputable section
namespace SerrePositivity
variable {A B : Type*} [CommRing A] [CommRing B]
    (p : ℕ) [Fact p.Prime] [CharP A p] [CharP B p]

/-- 第0成分を指定したperfectionの持ち上げ。核のFrobeniusの全射性が誤差を除く。 -/
theorem exists_perfection_lift_of_kernel_roots (f : A →+* B) (hf : Function.Surjective f)
    (hroots : ∀ a : A, f a = 0 → ∃ b : A, f b = 0 ∧ b ^ p = a)
    (y : Perfection B p) (b : A) (hb : f b = Perfection.coeff B p 0 y) :
    ∃ x : Perfection A p, Perfection.map p f x = y ∧ Perfection.coeff A p 0 x = b := by
  have hstep : ∀ n a, f a = Perfection.coeff B p n y →
      ∃ c : A, f c = Perfection.coeff B p (n + 1) y ∧ c ^ p = a := by
    intro n a ha
    obtain ⟨c, hc⟩ := hf (Perfection.coeff B p (n + 1) y)
    have herr : f (c ^ p - a) = 0 := by
      rw [map_sub, map_pow, hc, Perfection.coeff_pow_p', ha, sub_self]
    obtain ⟨t, ht, htp⟩ := hroots _ herr
    refine ⟨c - t, ?_, ?_⟩
    · rw [map_sub, hc, ht, sub_zero]
    · rw [sub_pow_char, htp]
      ring
  let L (n : ℕ) := {a : A // f a = Perfection.coeff B p n y}
  let step (n : ℕ) (a : L n) : L (n + 1) :=
    ⟨Classical.choose (hstep n a.val a.property), (Classical.choose_spec
      (hstep n a.val a.property)).1⟩
  let a : ∀ n, L n := fun n ↦ Nat.rec (⟨b, hb⟩ : L 0) step n
  have ha (n : ℕ) : (a (n + 1)).val ^ p = (a n).val := by
    change (Classical.choose (hstep n (a n).val (a n).property)) ^ p = (a n).val
    exact (Classical.choose_spec (hstep n (a n).val (a n).property)).2
  refine ⟨⟨fun n ↦ (a n).val, ha⟩, ?_, rfl⟩
  ext n
  exact (a n).property

/-- この条件の下で、perfection上の射も全射。 -/
theorem perfection_map_surjective_of_kernel_roots (f : A →+* B)
    (hf : Function.Surjective f)
    (hroots : ∀ a : A, f a = 0 → ∃ b : A, f b = 0 ∧ b ^ p = a) :
    Function.Surjective (Perfection.map p f) := by
  intro y
  obtain ⟨b, hb⟩ := hf (Perfection.coeff B p 0 y)
  obtain ⟨x, hx, _⟩ := exists_perfection_lift_of_kernel_roots p f hf hroots y b hb
  exact ⟨x, hx⟩

/-- 第0射影の核はperfection上の全射で像へ移る。第0成分を零として持ち上げる。 -/
theorem perfection_map_coeff_zero_kernel (f : A →+* B) (hf : Function.Surjective f)
    (hroots : ∀ a : A, f a = 0 → ∃ b : A, f b = 0 ∧ b ^ p = a) :
    (RingHom.ker (Perfection.coeff A p 0)).map (Perfection.map p f) =
      RingHom.ker (Perfection.coeff B p 0) := by
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    intro x hx
    change Perfection.coeff B p 0 (Perfection.map p f x) = 0
    rw [Perfection.coeff_map, show Perfection.coeff A p 0 x = 0 from hx, map_zero]
  · intro y hy
    obtain ⟨x, hx, hx0⟩ := exists_perfection_lift_of_kernel_roots p f hf hroots y 0
      (by rw [map_zero]; exact hy.symm)
    rw [← hx]
    exact Ideal.mem_map_of_mem _ hx0

end SerrePositivity
