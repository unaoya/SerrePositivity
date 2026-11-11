module

public import Mathlib.AlgebraicTopology.SimplicialSet.Homotopy

public import SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.SegmentWords
public import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.ParameterCube

/-!
# 中断した任意モデル源への一般化：WordSegment

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：A simplicial monoid segment built from finite interval words。

## 方針（定義・証明）
自由単体的分解・Dwyer–Kan型の生成射による整合化に対応する技法。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0617][inventory]を参照する。

[inventory]: ../../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0617
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# A simplicial monoid segment built from finite interval words

Zero interval letters become the unit, and one interval letters become an
absorbing zero. The underlying simplicial set stays in the interval universe.
-/

@[expose] public section
universe v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open CategoryTheory.CartesianMonoidalCategory

namespace SerrePositivity.SimplicialModel.WordSegment
abbrev interval : SSet.{v} := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.interval

def endpoint (n : SimplexCategoryᵒᵖ) (b : Fin 2) : interval.{v}.obj n :=
  SSet.stdSimplex.objEquiv.symm (SimplexCategory.Hom.mk (OrderHom.const _ b))

lemma endpoint_natural {n m : SimplexCategoryᵒᵖ} (θ : n ⟶ m) (b : Fin 2) :
    interval.{v}.map θ (endpoint n b) = endpoint m b := rfl

lemma endpoint_ne (n : SimplexCategoryᵒᵖ) : endpoint.{v} n 0 ≠ endpoint n 1 := by
  intro h
  have hh := congrArg (fun a : interval.{v}.obj n => (SSet.stdSimplex.objEquiv a).toOrderHom 0) h
  exact (by decide : (0 : Fin 2) ≠ 1) hh

abbrev degree (n : SimplexCategoryᵒᵖ) :=
  SegmentWords.Word (interval.{v}.obj n) (endpoint n 0) (endpoint n 1)

def degreeMap {n m : SimplexCategoryᵒᵖ} (θ : n ⟶ m) : degree.{v} n →*₀ degree m :=
  SegmentWords.map (fun x => interval.map θ x)

abbrev obj : SSet.{v} where
  obj n := degree n
  map θ := ↾(degreeMap θ)
  map_id n := by
    apply ConcreteCategory.hom_ext
    intro x
    have h : (fun a => interval.{v}.map (𝟙 n) a) = id := by
      funext a
      exact types_congr_hom (interval.map_id n) a
    change SegmentWords.map (fun a => interval.map (𝟙 n) a) x = x
    rw [h, SegmentWords.map_id (endpoint_ne n)]
    rfl
  map_comp {a b c} f g := by
    apply ConcreteCategory.hom_ext
    intro x
    have h : (fun y => interval.{v}.map (f ≫ g) y) =
        (fun y => interval.map g (interval.map f y)) := by
      funext y
      exact types_congr_hom (interval.map_comp f g) y
    have hm : degreeMap.{v} (f ≫ g) = (degreeMap g).comp (degreeMap f) := by
      unfold degreeMap
      rw [h]
      exact SegmentWords.map_comp (endpoint_ne b) (endpoint_ne c)
        (fun y => interval.map f y) (fun y => interval.map g y)
        (endpoint_natural f 0) (endpoint_natural f 1) (endpoint_natural g 0) (endpoint_natural g 1)
    exact congrArg (fun F : degree.{v} a →*₀ degree c => F x) hm

def letter : interval.{v} ⟶ obj where
  app n := ↾(SegmentWords.letter (endpoint n 0) (endpoint n 1))
  naturality {n m} θ := by
    apply ConcreteCategory.hom_ext
    intro x
    exact (SegmentWords.map_letter (endpoint_ne m) (fun a => interval.map θ a)
      (endpoint_natural θ 0) (endpoint_natural θ 1) x).symm

def mul : obj.{v} ⊗ obj ⟶ obj where
  app _ := ↾fun x => x.1 * x.2
  naturality {n m} θ := by
    apply ConcreteCategory.hom_ext
    intro x
    exact (map_mul (degreeMap θ) x.1 x.2).symm

def unit : SSet.stdSimplex.{v}.obj (SimplexCategory.mk 0) ⟶ obj where
  app _ := ↾fun _ => 1
  naturality {n m} θ := by
    apply ConcreteCategory.hom_ext
    intro _
    exact (map_one (degreeMap θ)).symm

def zero : SSet.stdSimplex.{v}.obj (SimplexCategory.mk 0) ⟶ obj where
  app _ := ↾fun _ => 0
  naturality {n m} θ := by
    apply ConcreteCategory.hom_ext
    intro _
    exact (map_zero (degreeMap θ)).symm

lemma letter_unit (n : SimplexCategoryᵒᵖ) : letter.{v}.app n (endpoint n 0) = 1 :=
  SegmentWords.letter_unit _ _

lemma letter_zero (n : SimplexCategoryᵒᵖ) : letter.{v}.app n (endpoint n 1) = 0 :=
  SegmentWords.letter_zero _ _ (endpoint_ne n)

lemma unit_ne_zero : unit.{v} ≠ zero := by
  intro h
  have hh := congr($(h).app (Opposite.op (SimplexCategory.mk 0))
    (SSet.stdSimplex.objEquiv.symm (𝟙 (SimplexCategory.mk 0))))
  exact (one_ne_zero : (1 : degree.{v} (Opposite.op (SimplexCategory.mk 0))) ≠ 0) hh

def unitAt (T : SSet.{v}) : T ⟶ obj := SSet.stdSimplex.isTerminalObj₀.from T ≫ unit

def zeroAt (T : SSet.{v}) : T ⟶ obj := SSet.stdSimplex.isTerminalObj₀.from T ≫ zero

lemma mul_assoc : mul.{v} ▷ obj ≫ mul = (α_ obj obj obj).hom ≫ obj ◁ mul ≫ mul := by
  ext n x
  exact _root_.mul_assoc x.1.1 x.1.2 x.2

lemma mul_unitAt {T : SSet.{v}} (a : T ⟶ obj) : lift a (unitAt T) ≫ mul = a := by
  ext n x
  exact mul_one (a.app n x)

lemma unitAt_mul {T : SSet.{v}} (a : T ⟶ obj) : lift (unitAt T) a ≫ mul = a := by
  ext n x
  exact one_mul (a.app n x)

lemma mul_zeroAt {T : SSet.{v}} (a : T ⟶ obj) : lift a (zeroAt T) ≫ mul = zeroAt T := by
  ext n x
  exact mul_zero (a.app n x)

lemma zeroAt_mul {T : SSet.{v}} (a : T ⟶ obj) : lift (zeroAt T) a ≫ mul = zeroAt T := by
  ext n x
  exact zero_mul (a.app n x)

lemma vertex_zero_letter : SSet.stdSimplex.δ (1 : Fin 2) ≫ letter.{v} = unit := by
  ext n x
  have hx : x = SSet.stdSimplex.objEquiv.symm
      (SimplexCategory.Hom.mk (OrderHom.const (Fin (n.unop.len + 1)) (0 : Fin 1))) := by
    apply SSet.stdSimplex.objEquiv.injective
    exact Subsingleton.elim _ _
  rw [hx]
  change letter.app n (endpoint n 0) = 1
  exact letter_unit n

lemma vertex_one_letter : SSet.stdSimplex.δ (0 : Fin 2) ≫ letter.{v} = zero := by
  ext n x
  have hx : x = SSet.stdSimplex.objEquiv.symm
      (SimplexCategory.Hom.mk (OrderHom.const (Fin (n.unop.len + 1)) (0 : Fin 1))) := by
    apply SSet.stdSimplex.objEquiv.injective
    exact Subsingleton.elim _ _
  rw [hx]
  change letter.app n (endpoint n 1) = 0
  exact letter_zero n

/-- Right multiplication by a moving interval letter contracts the word segment to zero. -/
def contraction : SSet.Homotopy (𝟙 obj.{v}) (zeroAt obj) where
  h := lift (fst obj interval) (snd obj interval ≫ letter) ≫ mul
  h₀ := by
    change SSet.ι₀ ≫ (lift (fst obj interval) (snd obj interval ≫ letter) ≫ mul) = 𝟙 obj
    ext n x
    change x * letter.app n (endpoint n 0) = x
    rw [letter_unit, mul_one]
  h₁ := by
    change SSet.ι₁ ≫ (lift (fst obj interval) (snd obj interval ≫ letter) ≫ mul) = zeroAt obj
    ext n x
    change x * letter.app n (endpoint n 1) = 0
    rw [letter_zero, mul_zero]
  rel := by
    apply NatTrans.ext
    funext n
    exact ConcreteCategory.hom_ext _ _ (fun x => False.elim x.1.property)

end SerrePositivity.SimplicialModel.WordSegment
