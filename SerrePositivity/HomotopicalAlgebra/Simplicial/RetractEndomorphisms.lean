module

public import SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.SegmentWords

/-!
# 中断した任意モデル源への一般化：RetractEndomorphisms

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類C）。
対象：Endomorphisms over a split retraction and under its section。

## 方針（定義・証明）
frameによる導来写像空間と整合図式の厳密化に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0549][inventory]を参照する。

[inventory]: ../../../formalization-plans/k-theory-generalization-inventory.md#m0549
[plan]: ../../../formalization-plans/k-theory.md
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Endomorphisms over a split retraction and under its section

Multiplication applies the left map first. The section-projection composite
is an absorbing zero. This is ordinary set-level algebra, with independent
universes and no model-category hypotheses.
-/

@[expose] public section
universe u v w z a b

namespace SerrePositivity.SimplicialModel.RetractEndomorphisms
variable {A : Type u} {B : Type v} (s : B → A) (p : A → B) (hs : Function.LeftInverse p s)

structure End (s : B → A) (p : A → B) (_hs : Function.LeftInverse p s) where
  toFun : A → A
  over : ∀ x, p (toFun x) = p x
  fixed : ∀ y, toFun (s y) = s y

instance : CoeFun (End s p hs) (fun _ => A → A) := ⟨End.toFun⟩

@[ext] lemma ext {f g : End s p hs} (h : ∀ x, f x = g x) : f = g := by
  cases f with
  | mk f hf hsf =>
    cases g with
    | mk g hg hsg =>
      have hh : f = g := funext h
      subst g
      rfl

instance : MonoidWithZero (End s p hs) where
  one := ⟨id, fun _ => rfl, fun _ => rfl⟩
  zero := ⟨s ∘ p, fun x => hs (p x), fun y => congrArg s (hs y)⟩
  mul f g := ⟨g ∘ f, fun x => (g.over (f x)).trans (f.over x),
    fun y => (congrArg g (f.fixed y)).trans (g.fixed y)⟩
  mul_assoc _ _ _ := by ext x; rfl
  one_mul _ := by ext x; rfl
  mul_one _ := by ext x; rfl
  zero_mul f := by ext x; exact f.fixed (p x)
  mul_zero f := by ext x; exact congrArg s (f.over x)

@[simp] lemma one_apply (x : A) : (1 : End s p hs) x = x := rfl
@[simp] lemma zero_apply (x : A) : (0 : End s p hs) x = s (p x) := rfl
@[simp] lemma mul_apply (f g : End s p hs) (x : A) : (f * g) x = g (f x) := rfl

lemma word_intertwining {A' : Type w} {B' : Type z}
    (s' : B' → A') (p' : A' → B') (hs' : Function.LeftInverse p' s')
    {I : Type a} {J : Type b} {eI zI : I} {eJ zJ : J} (hJ : eJ ≠ zJ)
    (f : I → J) (he : f eI = eJ) (hz : f zI = zJ)
    (φ : SegmentWords.Word I eI zI →*₀ End s p hs)
    (ψ : SegmentWords.Word J eJ zJ →*₀ End s' p' hs') (q : A → A')
    (h0 : ∀ x, q ((0 : End s p hs) x) = (0 : End s' p' hs') (q x))
    (hletter : ∀ i x, q (φ (SegmentWords.letter eI zI i) x) =
      ψ (SegmentWords.letter eJ zJ (f i)) (q x))
    (t : SegmentWords.Word I eI zI) (x : A) :
    q (φ t x) = ψ (SegmentWords.map f t) (q x) := by
  induction t using WithZero.recZeroCoe generalizing x with
  | zero => simpa only [map_zero] using h0 x
  | coe t =>
    induction t using FreeMonoid.recOn generalizing x with
    | one => simp only [WithZero.coe_one, map_one, one_apply]
    | of_mul i t ih =>
      change q (φ ((FreeMonoid.of i : SegmentWords.Word I eI zI) *
          (t : SegmentWords.Word I eI zI)) x) =
        ψ (SegmentWords.map f ((FreeMonoid.of i : SegmentWords.Word I eI zI) *
          (t : SegmentWords.Word I eI zI))) (q x)
      rw [← SegmentWords.letter_interior eI zI i]
      simp only [map_mul, mul_apply, SegmentWords.map_letter hJ f he hz]
      rw [ih, hletter]

end SerrePositivity.SimplicialModel.RetractEndomorphisms
