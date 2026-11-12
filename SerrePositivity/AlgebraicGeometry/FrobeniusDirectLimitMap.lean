module

public import SerrePositivity.AlgebraicGeometry.FrobeniusDirectLimit

/-!
概要：環の射による Frobenius 順極限の射と、核・像による全単射の判定。
方針：有限段の元を表示し、零判定と p 冪の像を用いる。
規約：零環を含め、各環で p = 0 だけを要求する。
使われ方：BST13 Lemma 3.5 の冪零不変性と普遍同相。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
universe u
variable {A B : Type u} [CommRing A] [CommRing B]
variable (p : ℕ) (hp : p.Prime) (hA : (p : A) = 0) (hB : (p : B) = 0)
variable (f : A →+* B)

/-- 環の射は各段の Frobenius の反復と可換。 -/
theorem frobeniusDirectSystemMap_naturality (i j : ℕ) (h : i ≤ j) (x : A) :
    f (frobeniusDirectSystemMap A p hp hA i j h x) =
      frobeniusDirectSystemMap B p hp hB i j h (f x) := by
  rw [frobeniusDirectSystemMap_apply, frobeniusDirectSystemMap_apply, map_pow]

/-- 実際の環の射が誘導する Frobenius 順極限の環準同型。 -/
def frobeniusDirectLimitMap :
    FrobeniusDirectLimit A p hp hA →+* FrobeniusDirectLimit B p hp hB :=
  DirectLimit.Ring.lift _ _ _ (fun n ↦ (frobeniusDirectLimitOf B p hp hB n).comp f)
    (fun i j h x ↦ by
      change frobeniusDirectLimitOf B p hp hB j
        (f (frobeniusDirectSystemMap A p hp hA i j h x)) = _
      rw [frobeniusDirectSystemMap_naturality p hp hA hB f i j h x]
      exact DirectLimit.Ring.of_f (G := fun _ : ℕ ↦ B)
        (f := frobeniusDirectSystemMap B p hp hB) h (f x))

/-- 順極限の射を有限段の元で評価する公式。 -/
@[simp] theorem frobeniusDirectLimitMap_of (n : ℕ) (x : A) :
    frobeniusDirectLimitMap p hp hA hB f (frobeniusDirectLimitOf A p hp hA n x) =
      frobeniusDirectLimitOf B p hp hB n (f x) := rfl

/-- 核が nil である環の射は、Frobenius 順極限上で単射になる。 -/
theorem frobeniusDirectLimitMap_injective
    (hk : ∀ a, f a = 0 → IsNilpotent a) :
    Function.Injective (frobeniusDirectLimitMap p hp hA hB f) := by
  apply (injective_iff_map_eq_zero (frobeniusDirectLimitMap p hp hA hB f)).mpr
  intro z hz
  obtain ⟨n, x, rfl⟩ := DirectLimit.exists_eq_mk (frobeniusDirectSystemMap A p hp hA) z
  change frobeniusDirectLimitOf A p hp hA n x = 0
  apply (frobeniusDirectLimitOf_eq_zero_iff_nilpotent A p hp hA n x).mpr
  have hx : IsNilpotent (f x) :=
    (frobeniusDirectLimitOf_eq_zero_iff_nilpotent B p hp hB n (f x)).mp hz
  obtain ⟨k, hkx⟩ := hx
  obtain ⟨l, hl⟩ := hk (x ^ k) (by rw [map_pow, hkx])
  exact ⟨k * l, by rw [pow_mul]; exact hl⟩

/-- 各元のある p 冪が像にある環の射は、Frobenius 順極限上で全射になる。 -/
theorem frobeniusDirectLimitMap_surjective
    (hs : ∀ b : B, ∃ e : ℕ, ∃ a : A, f a = b ^ (p ^ e)) :
    Function.Surjective (frobeniusDirectLimitMap p hp hA hB f) := by
  intro z
  obtain ⟨n, b, rfl⟩ := DirectLimit.exists_eq_mk (frobeniusDirectSystemMap B p hp hB) z
  obtain ⟨e, a, ha⟩ := hs b
  refine ⟨frobeniusDirectLimitOf A p hp hA (n + e) a, ?_⟩
  rw [frobeniusDirectLimitMap_of, ha]
  have hh := DirectLimit.Ring.of_f (G := fun _ : ℕ ↦ B)
    (f := frobeniusDirectSystemMap B p hp hB) (Nat.le_add_right n e) b
  simpa only [frobeniusDirectSystemMap_apply, Nat.add_sub_cancel_left,
    frobeniusDirectLimitOf, DirectLimit.Ring.of_apply] using hh

/-- Frobenius 順極限の射は環準同型の合成を保つ。 -/
theorem frobeniusDirectLimitMap_comp {C : Type u} [CommRing C]
    (hC : (p : C) = 0) (g : B →+* C) :
    (frobeniusDirectLimitMap p hp hB hC g).comp
        (frobeniusDirectLimitMap p hp hA hB f) =
      frobeniusDirectLimitMap p hp hA hC (g.comp f) := by
  apply DirectLimit.Ring.hom_ext
  intro n
  ext x
  rfl

/-- Frobenius 順極限の射は恒等射を保つ。 -/
theorem frobeniusDirectLimitMap_id :
    frobeniusDirectLimitMap p hp hA hA (RingHom.id A) =
      RingHom.id (FrobeniusDirectLimit A p hp hA) := by
  apply DirectLimit.Ring.hom_ext
  intro n
  ext x
  rfl

end SerrePositivity.AlgebraicGeometry
