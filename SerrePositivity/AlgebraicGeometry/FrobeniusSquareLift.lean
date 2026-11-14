module

public import SerrePositivity.AlgebraicGeometry.FrobeniusDirectLimitMap

/-!
概要：環の四角形の有限段の持ち上げを Frobenius 順極限に移す。
方針：順極限での一致を有限段へ戻し、そこで持ち上げる。
規約：有限段の持ち上げは明示した入力であり、導手の存在を仮定から隠さない。
使われ方：導手の四角形の完全性。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
universe u
variable {A B C D : Type u} [CommRing A] [CommRing B] [CommRing C] [CommRing D]
variable (p : ℕ) (hp : p.Prime)
variable (hA : (p : A) = 0) (hB : (p : B) = 0)
variable (hC : (p : C) = 0) (hD : (p : D) = 0)
variable (f : A →+* B) (g : A →+* C) (h : B →+* D) (k : C →+* D)

/-- 同じ有限段の二つの元が順極限の四角形で一致すれば、有限段の持ち上げを使える。 -/
theorem frobeniusSquare_lift_same_stage
    (hlift : ∀ b c, h b = k c → ∃ a, f a = b ∧ g a = c)
    (n : ℕ) (b : B) (c : C)
    (he : frobeniusDirectLimitOf D p hp hD n (h b) =
      frobeniusDirectLimitOf D p hp hD n (k c)) :
    ∃ a : FrobeniusDirectLimit A p hp hA,
      frobeniusDirectLimitMap p hp hA hB f a = frobeniusDirectLimitOf B p hp hB n b ∧
      frobeniusDirectLimitMap p hp hA hC g a = frobeniusDirectLimitOf C p hp hC n c := by
  obtain ⟨m, hn, hn', hm⟩ :=
    (frobeniusDirectLimitOf_eq_iff D p hp hD n n (h b) (k c)).mp he
  have he' : h (frobeniusDirectSystemMap B p hp hB n m hn b) =
      k (frobeniusDirectSystemMap C p hp hC n m hn c) := by
    rw [frobeniusDirectSystemMap_naturality p hp hB hD h,
      frobeniusDirectSystemMap_naturality p hp hC hD k]
    exact hm
  obtain ⟨a, ha, hc⟩ := hlift _ _ he'
  refine ⟨frobeniusDirectLimitOf A p hp hA m a, ?_, ?_⟩
  · rw [frobeniusDirectLimitMap_of, ha]
    exact DirectLimit.Ring.of_f (G := fun _ : ℕ ↦ B)
      (f := frobeniusDirectSystemMap B p hp hB) hn b
  · rw [frobeniusDirectLimitMap_of, hc]
    exact DirectLimit.Ring.of_f (G := fun _ : ℕ ↦ C)
      (f := frobeniusDirectSystemMap C p hp hC) hn c

/-- 有限段で持ち上げ可能な環の四角形は、Frobenius 順極限でも持ち上げ可能。 -/
theorem frobeniusSquare_lift
    (hlift : ∀ b c, h b = k c → ∃ a, f a = b ∧ g a = c)
    (x : FrobeniusDirectLimit B p hp hB) (y : FrobeniusDirectLimit C p hp hC)
    (he : frobeniusDirectLimitMap p hp hB hD h x =
      frobeniusDirectLimitMap p hp hC hD k y) :
    ∃ a : FrobeniusDirectLimit A p hp hA,
      frobeniusDirectLimitMap p hp hA hB f a = x ∧
      frobeniusDirectLimitMap p hp hA hC g a = y := by
  obtain ⟨n, b, rfl⟩ := DirectLimit.exists_eq_mk (frobeniusDirectSystemMap B p hp hB) x
  obtain ⟨m, c, rfl⟩ := DirectLimit.exists_eq_mk (frobeniusDirectSystemMap C p hp hC) y
  let t := max n m
  let b' := frobeniusDirectSystemMap B p hp hB n t (le_max_left n m) b
  let c' := frobeniusDirectSystemMap C p hp hC m t (le_max_right n m) c
  have hb : frobeniusDirectLimitOf B p hp hB t b' =
      frobeniusDirectLimitOf B p hp hB n b :=
    DirectLimit.Ring.of_f (G := fun _ : ℕ ↦ B)
      (f := frobeniusDirectSystemMap B p hp hB) (le_max_left n m) b
  have hc : frobeniusDirectLimitOf C p hp hC t c' =
      frobeniusDirectLimitOf C p hp hC m c :=
    DirectLimit.Ring.of_f (G := fun _ : ℕ ↦ C)
      (f := frobeniusDirectSystemMap C p hp hC) (le_max_right n m) c
  have he' : frobeniusDirectLimitOf D p hp hD t (h b') =
      frobeniusDirectLimitOf D p hp hD t (k c') := by
    change frobeniusDirectLimitMap p hp hB hD h (frobeniusDirectLimitOf B p hp hB t b') =
      frobeniusDirectLimitMap p hp hC hD k (frobeniusDirectLimitOf C p hp hC t c')
    rw [hb, hc]
    exact he
  obtain ⟨a, ha, ha'⟩ := frobeniusSquare_lift_same_stage p hp hA hB hC hD
    f g h k hlift t b' c' he'
  exact ⟨a, ha.trans hb, ha'.trans hc⟩

end SerrePositivity.AlgebraicGeometry
