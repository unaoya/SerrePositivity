module

public import SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.KanComparisonTetrahedron

/-!
# 中断した任意モデル源への一般化：KanComparisonSquare

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：A coherent four-sided comparison using one shared diagonal。

## 方針（定義・証明）
frameによる導来写像空間と整合図式の厳密化に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0407][inventory]を参照する。

[inventory]: ../../../../formalization-plans/k-theory-generalization-inventory.md#m0407
[plan]: ../../../../formalization-plans/k-theory.md
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# A coherent four-sided comparison using one shared diagonal

Two tetrahedra preserve four previously selected cone triangles. Their
remaining faces share the same actual diagonal and preserve the four
original comparison intervals. The output is a specified triangulated
disc; no extension of an arbitrary Kan boundary is asserted.
-/

@[expose] public section
universe v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed

namespace SerrePositivity.SimplicialModel.KanComparisonSquare
open KanComparisonTriangle
variable {T K : SSet.{v}} {f₀ f₁ f₂ f₃ z : T ⟶ K}
  (F₀ : SSet.Homotopy f₀ z) (F₁ : SSet.Homotopy f₁ z)
  (F₂ : SSet.Homotopy f₂ z) (F₃ : SSet.Homotopy f₃ z)
  (a : Data F₀ F₁) (b : Data F₁ F₂) (c : Data F₀ F₃) (d : Data F₃ F₂)

structure Filler where
  diagonal : Data F₀ F₂
  left : KanComparisonTetrahedron.Filler F₀ F₁ F₂ a diagonal b
  right : KanComparisonTetrahedron.Filler F₀ F₃ F₂ c diagonal d

variable (hK : SSet.modelCategoryQuillen.J.rlp (terminal.from K))

def build : Filler F₀ F₁ F₂ F₃ a b c d :=
  let e := KanComparisonTriangle.build F₀ F₂ hK
  ⟨e, KanComparisonTetrahedron.build F₀ F₁ F₂ a e b hK,
    KanComparisonTetrahedron.build F₀ F₃ F₂ c e d hK⟩

variable (q : Filler F₀ F₁ F₂ F₃ a b c d)

abbrev left : T ⊗ SSet.stdSimplex.obj (SimplexCategory.mk 2) ⟶ K :=
  KanComparisonTetrahedron.coherence F₀ F₁ F₂ a q.diagonal b q.left

abbrev right : T ⊗ SSet.stdSimplex.obj (SimplexCategory.mk 2) ⟶ K :=
  KanComparisonTetrahedron.coherence F₀ F₃ F₂ c q.diagonal d q.right

lemma left_first : T ◁ SSet.stdSimplex.δ (2 : Fin 3) ≫ left F₀ F₁ F₂ F₃ a b c d q =
    (comparison F₀ F₁ a).h := KanComparisonTetrahedron.coherence_two _ _ _ _ _ _ _

lemma left_second : T ◁ SSet.stdSimplex.δ (0 : Fin 3) ≫ left F₀ F₁ F₂ F₃ a b c d q =
    (comparison F₁ F₂ b).h := KanComparisonTetrahedron.coherence_zero _ _ _ _ _ _ _

lemma right_first : T ◁ SSet.stdSimplex.δ (2 : Fin 3) ≫ right F₀ F₁ F₂ F₃ a b c d q =
    (comparison F₀ F₃ c).h := KanComparisonTetrahedron.coherence_two _ _ _ _ _ _ _

lemma right_second : T ◁ SSet.stdSimplex.δ (0 : Fin 3) ≫ right F₀ F₁ F₂ F₃ a b c d q =
    (comparison F₃ F₂ d).h := KanComparisonTetrahedron.coherence_zero _ _ _ _ _ _ _

lemma common_diagonal : T ◁ SSet.stdSimplex.δ (1 : Fin 3) ≫ left F₀ F₁ F₂ F₃ a b c d q =
    T ◁ SSet.stdSimplex.δ (1 : Fin 3) ≫ right F₀ F₁ F₂ F₃ a b c d q := by
  rw [left, right, KanComparisonTetrahedron.coherence_one, KanComparisonTetrahedron.coherence_one]

end SerrePositivity.SimplicialModel.KanComparisonSquare
