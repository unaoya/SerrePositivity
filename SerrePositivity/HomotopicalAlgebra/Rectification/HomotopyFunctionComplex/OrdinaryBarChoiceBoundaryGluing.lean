module

public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryBarChoiceTriangleGluing

/-!
# 中断した任意モデル源への一般化：OrdinaryBarChoiceBoundaryGluing

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：All-degree gluing of actual parameterized choice morphisms。

## 方針（定義・証明）
自明fibrationのファイバーと相対延長による選択の比較に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0139][inventory]を参照する。

[inventory]: ../../../../formalization-plans/k-theory-generalization-inventory.md#m0139
[plan]: ../../../../formalization-plans/k-theory.md
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# All-degree gluing of actual parameterized choice morphisms

The face-overlap equalities imply equality of the underlying base arrows.
After relabeling to face zero, tensor-boundary gluing gives a single choice
morphism whose restrictions are the original, unnormalized faces.
-/

@[expose] public section
universe v u r
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.MonoidalCategory
open SerrePositivity.SimplicialModel

namespace SerrePositivity.HomotopyFunctionComplex.OrdinaryBarChoiceBoundaryGluing
abbrev parameters (P : SSet.{r}) (n : ℕ) := P ⊗ SSet.stdSimplex.obj (SimplexCategory.mk n)

variable {C : Type u} [Category.{v} C] [HomotopicalAlgebra.ModelCategory C]
  [HomotopicalAlgebra.ModelCategory SSet.{v}]
  (hcof : HomotopicalAlgebra.cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : HomotopicalAlgebra.fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
  {P : SSet.{max u v}} (n : ℕ)
  {X Y : OrdinaryBarChoiceCategory.Object (C := C) hcof hfib (parameters P (n + 1))}
  (a : Fin (n + 3) → (X ⟶ Y))

def Compatible : Prop := ∀ (j k : Fin (n + 3)) (hjk : j < k),
  (OrdinaryBarChoiceCategory.reindex hcof hfib
    (P ◁ SSet.stdSimplex.δ (k.pred (Fin.ne_zero_of_lt hjk)))).map (a j) =
  (OrdinaryBarChoiceCategory.reindex hcof hfib
    (P ◁ SSet.stdSimplex.δ (j.castPred (Fin.ne_last_of_lt hjk)))).map (a k)

variable (h : Compatible hcof hfib n a)

include h in
lemma base_eq (k : Fin (n + 3)) : (a k).base = (a 0).base := by
  by_cases hk : k = 0
  · subst k; rfl
  · exact (congrArg OrdinaryBarChoiceCategory.Hom.base
      (h 0 k (Fin.pos_iff_ne_zero.mpr hk))).symm

def faces (k : Fin (n + 3)) :
    parameters P (n + 1) ⟶ OrdinaryBarRetractSystem.choices hcof hfib (a 0).base :=
  (a k).extension ≫ OrdinaryBarChoiceComposition.relabel hcof hfib (base_eq hcof hfib n a h k)

set_option maxHeartbeats 800000 in
-- Normalizing the dependent choice types compares two proofs of base-arrow equality.
lemma faces_compatible : BoundaryTensorGluing.Compatible (faces hcof hfib n a h) := by
  intro j k hjk
  simpa only [faces, OrdinaryBarChoiceTriangleGluing.reindex_extension, Category.assoc] using
    OrdinaryBarChoiceTriangleGluing.normalized_extension_eq hcof hfib
      ((OrdinaryBarChoiceCategory.reindex hcof hfib
        (P ◁ SSet.stdSimplex.δ (k.pred (Fin.ne_zero_of_lt hjk)))).map (a j))
      ((OrdinaryBarChoiceCategory.reindex hcof hfib
        (P ◁ SSet.stdSimplex.δ (j.castPred (Fin.ne_last_of_lt hjk)))).map (a k))
      (h j k hjk) (a 0).base (base_eq hcof hfib n a h j) (base_eq hcof hfib n a h k)

def boundary : P ⊗ (SSet.boundary (n + 2)).toSSet ⟶
    OrdinaryBarRetractSystem.choices hcof hfib (a 0).base :=
  BoundaryTensorGluing.desc (faces hcof hfib n a h) (faces_compatible hcof hfib n a h)

lemma boundary_face (k : Fin (n + 3)) :
    P ◁ SSet.boundary.ι k ≫ boundary hcof hfib n a h = faces hcof hfib n a h k :=
  BoundaryTensorGluing.desc_fac _ _ k

def boundaryObject
    (Z : OrdinaryBarChoiceCategory.Object (C := C) hcof hfib (parameters P (n + 1))) :
    OrdinaryBarChoiceCategory.Object (C := C) hcof hfib
      (P ⊗ (SSet.boundary (n + 2)).toSSet) := ⟨Z.base⟩

def boundaryHom : boundaryObject hcof hfib n X ⟶ boundaryObject hcof hfib n Y :=
  ⟨(a 0).base, boundary hcof hfib n a h⟩

lemma boundaryHom_face (k : Fin (n + 3)) :
    (OrdinaryBarChoiceCategory.reindex hcof hfib (P ◁ SSet.boundary.ι k)).map
      (boundaryHom hcof hfib n a h) = a k := by
  exact (congrArg (fun s => (⟨(a 0).base, s⟩ : X ⟶ Y))
    (boundary_face hcof hfib n a h k)).trans
      (OrdinaryBarFreeDiagramHomotopy.normalized_eq hcof hfib (a 0) (a k)
        (base_eq hcof hfib n a h k))

end SerrePositivity.HomotopyFunctionComplex.OrdinaryBarChoiceBoundaryGluing
