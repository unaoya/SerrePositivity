module

public import Mathlib.Algebra.Ring.Hom.Defs

/-!
# 有界な p 冪ねじれ

BS 著者版 Definition 1.4・Definition 3.2 の有界性に使う述語。
環の全体がねじれであることは要求せず、ねじれ元の指数だけを一様に制限する。
-/

@[expose] public section
universe u
namespace SerrePositivity

/-- BS 著者版 Definition 1.4 の有界な p 冪ねじれ。
ある固定の p^N が、各々ある p 冪で消える元をすべて消す。
素数性はこの述語の定義には不要。prism の剰余環の有界性を表す。 -/
def HasBoundedPTorsion (p : ℕ) (R : Type u) [CommRing R] : Prop :=
  ∃ N : ℕ, ∀ (n : ℕ) (x : R), (p : R) ^ n * x = 0 → (p : R) ^ N * x = 0

/-- ねじれ指数の上界を指定すれば有界性を得る。定義を展開した構成則。 -/
theorem HasBoundedPTorsion.of_bound {p : ℕ} {R : Type u} [CommRing R] (N : ℕ)
    (h : ∀ (n : ℕ) (x : R), (p : R) ^ n * x = 0 → (p : R) ^ N * x = 0) :
    HasBoundedPTorsion p R := ⟨N, h⟩

/-- 有界性から一様な指数を取り出す。個別のねじれ指数に依存しない。 -/
theorem HasBoundedPTorsion.exists_bound {p : ℕ} {R : Type u} [CommRing R]
    (h : HasBoundedPTorsion p R) :
    ∃ N : ℕ, ∀ (n : ℕ) (x : R), (p : R) ^ n * x = 0 → (p : R) ^ N * x = 0 := h

end SerrePositivity
