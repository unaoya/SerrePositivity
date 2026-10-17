module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.RelativeProductLifting

/-!
# 中断した任意モデル源への一般化：RelativeBoundaryFilling

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：Fill a whole compatible boundary over a fixed base, relative to fixed inputs。

## 方針（定義・証明）
自明fibrationのファイバーと相対延長による選択の比較に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0534][inventory]を参照する。

[inventory]: ../../../formalization-plans/k-theory-generalization-inventory.md#m0534
[plan]: ../../../formalization-plans/k-theory.md
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Fill a whole compatible boundary over a fixed base, relative to fixed inputs

All previously specified faces are retained as actual maps. A single
choice is made before restriction to any external parameter. The same
construction applies in every dimension at least two.
-/

@[expose] public section
universe v
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory

namespace SerrePositivity.SimplicialModel.RelativeBoundaryFilling
variable {E B A X : SSet.{v}} (p : E ⟶ B)
  (hp : (MorphismProperty.monomorphisms SSet.{v}).rlp p)
  (i : A ⟶ X) [Mono i] (a : A ⟶ E) (b : X ⟶ B) (hab : a ≫ p = i ≫ b)
  {n : ℕ}
  (faces : Fin (n + 3) → (X ⊗ SSet.stdSimplex.obj (SimplexCategory.mk (n + 1)) ⟶ E))
  (hc : BoundaryTensorGluing.Compatible faces)
  (hb : ∀ k, faces k ≫ p = fst X _ ≫ b)
  (ha : ∀ k, i ▷ SSet.stdSimplex.obj (SimplexCategory.mk (n + 1)) ≫ faces k =
    fst A _ ≫ a)

omit [Mono i] in
include hc ha in
lemma boundary_compatible : i ▷ (SSet.boundary (n + 2)).toSSet ≫
    BoundaryTensorGluing.desc faces hc =
    A ◁ (SSet.boundary (n + 2)).ι ≫
      (fst A (SSet.stdSimplex.obj (SimplexCategory.mk (n + 2))) ≫ a) := by
  apply BoundaryTensorGluing.hom_ext
  intro k
  have hx : A ◁ SSet.boundary.ι k ≫ i ▷ (SSet.boundary (n + 2)).toSSet =
      i ▷ SSet.stdSimplex.obj (SimplexCategory.mk (n + 1)) ≫ X ◁ SSet.boundary.ι k :=
    whisker_exchange i (SSet.boundary.ι k)
  rw [← Category.assoc, hx, Category.assoc, BoundaryTensorGluing.desc_fac, ha k]
  ext m x
  rfl

include hc hb in
lemma boundary_base : BoundaryTensorGluing.desc faces hc ≫ p =
    X ◁ (SSet.boundary (n + 2)).ι ≫
      (fst X (SSet.stdSimplex.obj (SimplexCategory.mk (n + 2))) ≫ b) := by
  apply BoundaryTensorGluing.hom_ext
  intro k
  rw [← Category.assoc, BoundaryTensorGluing.desc_fac, hb k]
  ext m x
  rfl

def filler : X ⊗ SSet.stdSimplex.obj (SimplexCategory.mk (n + 2)) ⟶ E :=
  RelativeProductLifting.lift p hp i (SSet.boundary (n + 2)).ι
    (BoundaryTensorGluing.desc faces hc) (fst A _ ≫ a) (fst X _ ≫ b)
    (boundary_compatible i a faces hc ha)
    (boundary_base p b faces hc hb)
    (by rw [Category.assoc, hab, whiskerRight_fst_assoc])

lemma filler_boundary : X ◁ (SSet.boundary (n + 2)).ι ≫
    filler p hp i a b hab faces hc hb ha = BoundaryTensorGluing.desc faces hc :=
  RelativeProductLifting.lift_earlier _ _ _ _ _ _ _ _ _ _

lemma filler_face (k : Fin (n + 3)) : X ◁ SSet.stdSimplex.δ k ≫
    filler p hp i a b hab faces hc hb ha = faces k := by
  rw [← SSet.boundary.ι_ι k, whiskerLeft_comp, Category.assoc, filler_boundary]
  exact BoundaryTensorGluing.desc_fac faces hc k

lemma filler_relative : i ▷ SSet.stdSimplex.obj (SimplexCategory.mk (n + 2)) ≫
    filler p hp i a b hab faces hc hb ha = fst A _ ≫ a :=
  RelativeProductLifting.lift_prescribed _ _ _ _ _ _ _ _ _ _

lemma filler_base : filler p hp i a b hab faces hc hb ha ≫ p = fst X _ ≫ b :=
  RelativeProductLifting.lift_base _ _ _ _ _ _ _ _ _ _

variable {T : SSet.{v}} (t : T ⟶ X)

abbrev family := t ▷ SSet.stdSimplex.obj (SimplexCategory.mk (n + 2)) ≫
  filler p hp i a b hab faces hc hb ha

lemma family_reindex {U : SSet.{v}} (j : U ⟶ T) :
    family p hp i a b hab faces hc hb ha (j ≫ t) =
      j ▷ SSet.stdSimplex.obj (SimplexCategory.mk (n + 2)) ≫
        family p hp i a b hab faces hc hb ha t := by
  dsimp only [family]
  rw [comp_whiskerRight, Category.assoc]

end SerrePositivity.SimplicialModel.RelativeBoundaryFilling
