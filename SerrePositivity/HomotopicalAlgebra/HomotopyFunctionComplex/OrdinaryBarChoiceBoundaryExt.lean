module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarChoiceTriangleGluing

/-!
# 中断した任意モデル源への一般化：OrdinaryBarChoiceBoundaryExt

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：Boundary choices are determined by their entire facet restrictions。

## 方針（定義・証明）
自明fibrationのファイバーと相対延長による選択の比較に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0138][inventory]を参照する。

[inventory]: ../../../formalization-plans/k-theory-generalization-inventory.md#m0138
[plan]: ../../../formalization-plans/k-theory.md
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Boundary choices are determined by their entire facet restrictions

This is joint faithfulness of the family of boundary restrictions. It does
not assert faithfulness of any individual restriction or base projection.
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.MonoidalCategory
open SerrePositivity.SimplicialModel

namespace SerrePositivity.HomotopyFunctionComplex.OrdinaryBarChoiceBoundaryExt
variable {C : Type u} [Category.{v} C] [HomotopicalAlgebra.ModelCategory C]
  [HomotopicalAlgebra.ModelCategory SSet.{v}]
  (hcof : HomotopicalAlgebra.cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : HomotopicalAlgebra.fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)

lemma hom_ext {P : SSet.{max u v}} {n : ℕ}
    {X Y : OrdinaryBarChoiceCategory.Object (C := C) hcof hfib
      (P ⊗ (SSet.boundary (n + 1)).toSSet)} (a b : X ⟶ Y)
    (h : ∀ k : Fin (n + 2),
      (OrdinaryBarChoiceCategory.reindex hcof hfib (P ◁ SSet.boundary.ι k)).map a =
        (OrdinaryBarChoiceCategory.reindex hcof hfib (P ◁ SSet.boundary.ι k)).map b) : a = b := by
  have hb := congrArg OrdinaryBarChoiceCategory.Hom.base (h 0)
  change a.base = b.base at hb
  cases a with | mk f s =>
    cases b with | mk g t =>
      dsimp only at hb
      subst g
      have he : s = t := by
        apply BoundaryTensorGluing.hom_ext
        intro k
        have hk := OrdinaryBarFreeDiagramHomotopy.extension_eq hcof hfib _ _ (h k) rfl
        simpa only [OrdinaryBarChoiceTriangleGluing.reindex_extension,
          OrdinaryBarChoiceTriangleGluing.relabel_refl, Category.comp_id] using hk
      subst t
      rfl

end SerrePositivity.HomotopyFunctionComplex.OrdinaryBarChoiceBoundaryExt
