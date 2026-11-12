module

public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
概要：導手の中にあるイデアルによる商の四角形の、有限段での持ち上げ。
方針：二つの元の差を導手から元の環へ持ち上げる。
規約：導手の存在や有限性からの冪の評価はこの補題の仮定と区別する。
使われ方：BST13 Lemma 3.8 の affine の四角形を Frobenius 順極限に移す計算。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
universe u
variable {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B)

/-- 導手に含まれるイデアルの商で一致する元は、元の環の同じ元から来る。 -/
theorem conductorSquare_lift (K : Ideal B) (hK : ∀ b ∈ K, ∃ a : A, f a = b)
    (a : A) (b : B) (h : Ideal.Quotient.mk K b = Ideal.Quotient.mk K (f a)) :
    ∃ c : A, f c = b ∧
      Ideal.Quotient.mk (K.comap f) c = Ideal.Quotient.mk (K.comap f) a := by
  have hdK : b - f a ∈ K := (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp h
  obtain ⟨d, hd⟩ := hK (b - f a) hdK
  refine ⟨a + d, ?_, ?_⟩
  · rw [map_add, hd]
    ring
  · apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr
    change f (a + d - a) ∈ K
    simpa only [add_sub_cancel_left, hd] using hdK

/-- 導手の四角形の左の射の核は、元の環準同型の核と同じ。 -/
theorem conductorSquare_kernel (K : Ideal B) (a : A) :
    (f a = 0 ∧ Ideal.Quotient.mk (K.comap f) a = 0) ↔ f a = 0 := by
  constructor
  · exact And.left
  · intro ha
    refine ⟨ha, Ideal.Quotient.eq_zero_iff_mem.mpr ?_⟩
    change f a ∈ K
    rw [ha]
    exact K.zero_mem

end SerrePositivity.AlgebraicGeometry
