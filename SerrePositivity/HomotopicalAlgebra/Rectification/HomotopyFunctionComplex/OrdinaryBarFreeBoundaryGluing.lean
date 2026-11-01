module

public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryBarChoiceBoundaryGluing

/-!
# 中断した任意モデル源への一般化：OrdinaryBarFreeBoundaryGluing

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：Assemble all faces into a whole free boundary diagram in every degree。

## 方針（定義・証明）
自由単体的分解・Dwyer–Kan型の生成射による整合化に対応する技法。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0172][inventory]を参照する。

[inventory]: ../../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0172
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Assemble all faces into a whole free boundary diagram in every degree

Only the actual face-overlap equalities on generators are inputs. Gluing
choice morphisms and extending freely gives equality of whole face functors,
including arbitrary composites and identity paths.
-/

@[expose] public section
universe v u vV uV
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.MonoidalCategory

namespace SerrePositivity.HomotopyFunctionComplex.OrdinaryBarFreeBoundaryGluing
open OrdinaryBarFreeDiagramExtension OrdinaryBarChoiceBoundaryGluing
variable {C : Type u} [Category.{v} C] [HomotopicalAlgebra.ModelCategory C]
  [HomotopicalAlgebra.ModelCategory SSet.{v}]
  (hcof : HomotopicalAlgebra.cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : HomotopicalAlgebra.fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
  {V : Type uV} [Quiver.{vV} V] {P : SSet.{max u v}} (n : ℕ)
  (φ : V ⥤q target (C := C) hcof hfib (parameters P (n + 1)))
  (a : Fin (n + 3) → {X Y : V} → (X ⟶ Y) → (φ.obj X ⟶ φ.obj Y))
  (h : ∀ {X Y : V} (e : X ⟶ Y), Compatible hcof hfib n (fun k => a k e))

def generators : V ⥤q target (C := C) hcof hfib (P ⊗ (SSet.boundary (n + 2)).toSSet) where
  obj X := boundaryObject hcof hfib n (φ.obj X)
  map e := boundaryHom hcof hfib n (fun k => a k e) (h e)

def boundary : Paths V ⥤ target (C := C) hcof hfib (P ⊗ (SSet.boundary (n + 2)).toSSet) :=
  Paths.lift (generators hcof hfib n φ a h)

def faceGenerators (k : Fin (n + 3)) :
    V ⥤q target (C := C) hcof hfib (parameters P (n + 1)) where
  obj X := φ.obj X
  map e := a k e

def faceDiagram (k : Fin (n + 3)) :
    Paths V ⥤ target (C := C) hcof hfib (parameters P (n + 1)) :=
  Paths.lift (faceGenerators hcof hfib n φ a k)

lemma boundary_face (k : Fin (n + 3)) : boundary hcof hfib n φ a h ⋙
    OrdinaryBarChoiceCategory.reindex hcof hfib (P ◁ SSet.boundary.ι k) =
      faceDiagram hcof hfib n φ a k := by
  refine Paths.ext_functor
    (F := boundary hcof hfib n φ a h ⋙
      OrdinaryBarChoiceCategory.reindex hcof hfib (P ◁ SSet.boundary.ι k))
    (G := faceDiagram hcof hfib n φ a k) rfl ?_
  intro X Y e
  simp only [CategoryTheory.Functor.comp_map, boundary, faceDiagram, Paths.lift_toPath,
    eqToHom_refl, Category.id_comp, Category.comp_id]
  exact OrdinaryBarChoiceBoundaryGluing.boundaryHom_face hcof hfib n (fun k => a k e) (h e) k

end SerrePositivity.HomotopyFunctionComplex.OrdinaryBarFreeBoundaryGluing
