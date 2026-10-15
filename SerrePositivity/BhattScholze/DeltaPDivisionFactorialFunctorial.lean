module

public import SerrePositivity.BhattScholze.DeltaPDivisionFactorialMap

/-! # 具体的階乗生成部分環の射の一意性と関手性 -/

@[expose] public noncomputable section
universe u v w z
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {σ : Type w}

omit [Fact p.Prime] in
/-- 基底と全階乗生成元上で一致する、具体的部分環からの環射は一致する。 -/
theorem pDivisionFactorialHom_ext {T : Type z} [CommRing T] (y : σ → A)
    (F G : pDivisionFactorialSubring p y →+* T)
    (hbase : ∀ a : A, F (pDivisionFactorialBase p y a) = G (pDivisionFactorialBase p y a))
    (hvalue : ∀ (s : σ) (n : ℕ),
      F ⟨pDivisionFactorialValue p y s n, pDivisionFactorialSubring_value_mem y s n⟩ =
      G ⟨pDivisionFactorialValue p y s n, pDivisionFactorialSubring_value_mem y s n⟩) : F = G := by
  apply RingHom.ext
  rintro ⟨t, ht⟩
  induction ht using Subring.closure_induction with
  | mem t ht =>
      rcases ht with (⟨a, rfl⟩ | ⟨⟨s, n⟩, rfl⟩)
      · exact hbase a
      · exact hvalue s n
  | zero => exact (map_zero F).trans (map_zero G).symm
  | one => exact (map_one F).trans (map_one G).symm
  | add x y hx hy ihx ihy =>
      change F (⟨x, hx⟩ + ⟨y, hy⟩) = G (⟨x, hx⟩ + ⟨y, hy⟩)
      rw [map_add, map_add, ihx, ihy]
  | neg x hx ih =>
      change F (-⟨x, hx⟩) = G (-⟨x, hx⟩)
      rw [map_neg, map_neg, ih]
  | mul x y hx hy ihx ihy =>
      change F (⟨x, hx⟩ * ⟨y, hy⟩) = G (⟨x, hx⟩ * ⟨y, hy⟩)
      rw [map_mul, map_mul, ihx, ihy]

/-- 基底の恒等射が誘導する実階乗部分環射は恒等射。 -/
theorem pDivisionFactorialMap_id (hlocal : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A)) (y : σ → A) :
    pDivisionFactorialMap hlocal (RingHom.id A) y = RingHom.id (pDivisionFactorialSubring p y) := by
  apply pDivisionFactorialHom_ext y
  · intro a
    exact RingHom.congr_fun (pDivisionFactorialMap_comp_base hlocal (RingHom.id A) y) a
  · intro s n
    exact pDivisionFactorialMap_value hlocal (RingHom.id A) y s n

/-- 基底の合成射が誘導する実階乗部分環射は、誘導射の合成と一致する。 -/
theorem pDivisionFactorialMap_comp {B : Type v} {C : Type z} [CommRing B] [CommRing C]
    (hA : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A))
    (hB : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : B)) (f : A →+* B) (g : B →+* C) (y : σ → A) :
    (pDivisionFactorialMap hB g (fun s ↦ f (y s))).comp (pDivisionFactorialMap hA f y) =
      pDivisionFactorialMap hA (g.comp f) y := by
  apply pDivisionFactorialHom_ext y
  · intro a
    change pDivisionFactorialMap hB g (fun s ↦ f (y s))
        (pDivisionFactorialMap hA f y (pDivisionFactorialBase p y a)) = _
    have hf := RingHom.congr_fun (pDivisionFactorialMap_comp_base hA f y) a
    have hg := RingHom.congr_fun (pDivisionFactorialMap_comp_base hB g (fun s ↦ f (y s))) (f a)
    have hgf := RingHom.congr_fun (pDivisionFactorialMap_comp_base hA (g.comp f) y) a
    simp only [RingHom.comp_apply] at hf hg hgf
    rw [hf, hg, hgf]
  · intro s n
    change pDivisionFactorialMap hB g (fun s ↦ f (y s))
        (pDivisionFactorialMap hA f y ⟨_, _⟩) = _
    rw [pDivisionFactorialMap_value, pDivisionFactorialMap_value, pDivisionFactorialMap_value]
    rfl

end SerrePositivity.BhattScholze
