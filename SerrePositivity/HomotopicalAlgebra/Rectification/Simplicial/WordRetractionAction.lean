module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.RetractEndomorphisms
public import SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.WordSegment

/-!
# 中断した任意モデル源への一般化：WordRetractionAction

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：Extend an actual strong contraction to a strict action of interval words。

## 方針（定義・証明）
自由単体的分解・Dwyer–Kan型の生成射による整合化に対応する技法。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0616][inventory]を参照する。

[inventory]: ../../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0616
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Extend an actual strong contraction to a strict action of interval words

The original interval contraction has no assumed semigroup law. The word
extension has a strict multiplication law and retains the original letter
values, the projection, and the section.
-/

@[expose] public section
universe v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory

namespace SerrePositivity.SimplicialModel.WordRetractionAction
variable {E B : SSet.{v}} (s : B ⟶ E) (p : E ⟶ B) (hs : s ≫ p = 𝟙 B)
  (H : SSet.Homotopy (𝟙 E) (p ≫ s))
  (hP : H.h ≫ p = fst E WordSegment.interval ≫ p)
  (hS : s ▷ WordSegment.interval ≫ H.h = fst B WordSegment.interval ≫ s)

include hs in
lemma split (n : SimplexCategoryᵒᵖ) :
    Function.LeftInverse (fun x => p.app n x) (fun y => s.app n y) :=
  fun y => types_congr_hom (congr_app hs n) y

abbrev EndAt (n : SimplexCategoryᵒᵖ) :=
  RetractEndomorphisms.End (fun y => s.app n y) (fun x => p.app n x) (split s p hs n)

def letterEnd (n : SimplexCategoryᵒᵖ) (t : WordSegment.interval.obj n) : EndAt s p hs n where
  toFun x := H.h.app n (x, t)
  over x := types_congr_hom (congr_app hP n) (x, t)
  fixed y := types_congr_hom (congr_app hS n) (y, t)

lemma letterEnd_unit (n : SimplexCategoryᵒᵖ) :
    letterEnd s p hs H hP hS n (WordSegment.endpoint n 0) = 1 := by
  apply RetractEndomorphisms.ext
  intro x
  exact types_congr_hom (congr_app H.h₀ n) x

lemma letterEnd_zero (n : SimplexCategoryᵒᵖ) :
    letterEnd s p hs H hP hS n (WordSegment.endpoint n 1) = 0 := by
  apply RetractEndomorphisms.ext
  intro x
  exact types_congr_hom (congr_app H.h₁ n) x

def eval (n : SimplexCategoryᵒᵖ) : WordSegment.degree n →*₀ EndAt s p hs n :=
  SegmentWords.lift (WordSegment.endpoint n 0) (WordSegment.endpoint n 1)
    (letterEnd s p hs H hP hS n)

lemma eval_letter (n : SimplexCategoryᵒᵖ) (t : WordSegment.interval.obj n) :
    eval s p hs H hP hS n (WordSegment.letter.app n t) = letterEnd s p hs H hP hS n t :=
  SegmentWords.lift_letter _ _ _ (letterEnd_unit s p hs H hP hS n)
    (letterEnd_zero s p hs H hP hS n) t

lemma eval_naturality {n m : SimplexCategoryᵒᵖ} (θ : n ⟶ m) (w : WordSegment.degree n)
    (x : E.obj n) : E.map θ (eval s p hs H hP hS n w x) =
      eval s p hs H hP hS m (WordSegment.degreeMap θ w) (E.map θ x) := by
  apply RetractEndomorphisms.word_intertwining
    (fun y => s.app n y) (fun x => p.app n x) (split s p hs n)
    (fun y => s.app m y) (fun x => p.app m x) (split s p hs m)
    (WordSegment.endpoint_ne m) (fun t => WordSegment.interval.map θ t)
    (WordSegment.endpoint_natural θ 0) (WordSegment.endpoint_natural θ 1)
    (eval s p hs H hP hS n) (eval s p hs H hP hS m) (fun x => E.map θ x)
  · intro y
    exact (types_congr_hom ((p ≫ s).naturality θ) y).symm
  · intro t y
    change E.map θ (eval s p hs H hP hS n (WordSegment.letter.app n t) y) =
      eval s p hs H hP hS m
        (WordSegment.letter.app m (WordSegment.interval.map θ t)) (E.map θ y)
    rw [eval_letter, eval_letter]
    exact (types_congr_hom (H.h.naturality θ) (y, t)).symm

def action : E ⊗ WordSegment.obj ⟶ E where
  app n := ↾fun x => eval s p hs H hP hS n x.2 x.1
  naturality {_ _} θ := by
    apply ConcreteCategory.hom_ext
    intro x
    exact (eval_naturality s p hs H hP hS θ x.2 x.1).symm

lemma action_letter : E ◁ WordSegment.letter ≫ action s p hs H hP hS = H.h := by
  ext n x
  exact congrArg (fun f : EndAt s p hs n => f x.1) (eval_letter s p hs H hP hS n x.2)

lemma action_mul : E ◁ WordSegment.mul ≫ action s p hs H hP hS =
    (α_ E WordSegment.obj WordSegment.obj).inv ≫
      action s p hs H hP hS ▷ WordSegment.obj ≫ action s p hs H hP hS := by
  ext n x
  change eval s p hs H hP hS n (x.2.1 * x.2.2) x.1 =
    eval s p hs H hP hS n x.2.2 (eval s p hs H hP hS n x.2.1 x.1)
  rw [map_mul]
  rfl

lemma action_unit {T : SSet.{v}} (a : T ⟶ E) :
    lift a (WordSegment.unitAt T) ≫ action s p hs H hP hS = a := by
  ext n x
  change eval s p hs H hP hS n 1 (a.app n x) = a.app n x
  rw [map_one, RetractEndomorphisms.one_apply]

lemma action_zero {T : SSet.{v}} (a : T ⟶ E) :
    lift a (WordSegment.zeroAt T) ≫ action s p hs H hP hS = a ≫ p ≫ s := by
  ext n x
  change eval s p hs H hP hS n 0 (a.app n x) = s.app n (p.app n (a.app n x))
  rw [map_zero, RetractEndomorphisms.zero_apply]

lemma action_over : action s p hs H hP hS ≫ p = fst E WordSegment.obj ≫ p := by
  ext n x
  exact (eval s p hs H hP hS n x.2).over x.1

lemma action_section : s ▷ WordSegment.obj ≫ action s p hs H hP hS =
    fst B WordSegment.obj ≫ s := by
  ext n x
  exact (eval s p hs H hP hS n x.2).fixed x.1

end SerrePositivity.SimplicialModel.WordRetractionAction
