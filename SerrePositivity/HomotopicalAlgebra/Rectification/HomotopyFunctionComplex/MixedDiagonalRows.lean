module

public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.MixedDiagonalHomTransport
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.DiagonalMappingWeakEquivalence

/-!
# 中断した任意モデル源への一般化：MixedDiagonalRows

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：Rowwise detection of weak equivalences on the actual mixed Hom。

## 方針（定義・証明）
frameによる導来写像空間と整合図式の厳密化に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0121][inventory]を参照する。

[inventory]: ../../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0121
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Rowwise detection of weak equivalences on the actual mixed Hom

The two row descriptions retain the actual arrows, using op/unop on the right.
Only the original small simplicial model structure is used.
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory HomotopicalAlgebra Opposite

namespace SerrePositivity.HomotopyFunctionComplex.MixedDiagonalRows
variable {C : Type u} [Category.{v} C]

abbrev leftRows (A : SimplexCategory ⥤ C) (B : SimplexCategory ⥤ Cᵒᵖ) :=
  B.leftOp ⋙ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom A

abbrev rightRows (A : SimplexCategory ⥤ C) (B : SimplexCategory ⥤ Cᵒᵖ) :=
  A.op ⋙ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom B

def leftIso (A : SimplexCategory ⥤ C) (B : SimplexCategory ⥤ Cᵒᵖ) :
    BisimplicialModel.diagonal.obj (leftRows A B) ≅ MixedDiagonalHom.obj A B :=
  NatIso.ofComponents (fun _ => (Equiv.refl _).toIso) (by
    intro n m θ
    ext h
    change A.map θ.unop ≫ h ≫ (B.map θ.unop).unop = _
    rfl)

def rightEquiv (A : SimplexCategory ⥤ C) (B : SimplexCategory ⥤ Cᵒᵖ)
    (n : SimplexCategoryᵒᵖ) :
    ((rightRows A B).obj n).obj n ≃ (MixedDiagonalHom.obj A B).obj n where
  toFun h := h.unop
  invFun h := h.op
  left_inv _ := rfl
  right_inv _ := rfl

def rightIso (A : SimplexCategory ⥤ C) (B : SimplexCategory ⥤ Cᵒᵖ) :
    BisimplicialModel.diagonal.obj (rightRows A B) ≅ MixedDiagonalHom.obj A B :=
  NatIso.ofComponents (fun n => (rightEquiv A B n).toIso) (by
    intro n m θ
    ext h
    change (B.map θ.unop ≫ h ≫ (A.map θ.unop).op).unop =
      A.map θ.unop ≫ h.unop ≫ (B.map θ.unop).unop
    simp only [unop_comp, Quiver.Hom.unop_op, Category.assoc])

def leftComparison {A D : SimplexCategory ⥤ C} (a : D ⟶ A)
    (B : SimplexCategory ⥤ Cᵒᵖ) : leftRows A B ⟶ leftRows D B :=
  Functor.whiskerLeft B.leftOp (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHomMap a)

def rightComparison (A : SimplexCategory ⥤ C) {B E : SimplexCategory ⥤ Cᵒᵖ}
    (b : E ⟶ B) : rightRows A B ⟶ rightRows A E :=
  Functor.whiskerLeft A.op (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHomMap b)

lemma left_comparison_eq {A D : SimplexCategory ⥤ C} (a : D ⟶ A)
    (B : SimplexCategory ⥤ Cᵒᵖ) :
    MixedDiagonalHom.map a (𝟙 B) = (leftIso A B).inv ≫
      BisimplicialModel.diagonal.map (leftComparison a B) ≫ (leftIso D B).hom := by
  ext n h
  change a.app n.unop ≫ h ≫ (𝟙 _).unop = a.app n.unop ≫ h
  simp only [unop_id, Category.comp_id]

lemma right_comparison_eq (A : SimplexCategory ⥤ C)
    {B E : SimplexCategory ⥤ Cᵒᵖ} (b : E ⟶ B) :
    MixedDiagonalHom.map (𝟙 A) b = (rightIso A B).inv ≫
      BisimplicialModel.diagonal.map (rightComparison A b) ≫ (rightIso A E).hom := by
  ext n h
  change 𝟙 _ ≫ h ≫ (b.app n.unop).unop = (b.app n.unop ≫ h.op).unop
  simp only [unop_comp, Quiver.Hom.unop_op, Category.id_comp]

variable [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)

include hcof hfib in
lemma left_weakEquivalence {A D : SimplexCategory ⥤ C} (a : D ⟶ A)
    (B : SimplexCategory ⥤ Cᵒᵖ)
    (ha : ∀ n : SimplexCategoryᵒᵖ, weakEquivalences SSet.{v}
      ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHomMap a).app (B.obj n.unop).unop)) :
    weakEquivalences SSet.{v} (MixedDiagonalHom.map a (𝟙 B)) := by
  rw [left_comparison_eq]
  exact (weakEquivalences SSet.{v}).comp_mem _ _
    ((weakEquivalences SSet.{v}).of_isIso (leftIso A B).inv)
    ((weakEquivalences SSet.{v}).comp_mem _ _
      (BisimplicialModel.diagonal_map_weakEquivalence hcof hfib (leftComparison a B) ha)
      ((weakEquivalences SSet.{v}).of_isIso (leftIso D B).hom))

include hcof hfib in
lemma right_weakEquivalence (A : SimplexCategory ⥤ C)
    {B E : SimplexCategory ⥤ Cᵒᵖ} (b : E ⟶ B)
    (hb : ∀ n : SimplexCategoryᵒᵖ, weakEquivalences SSet.{v}
      ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHomMap b).app (op (A.obj n.unop)))) :
    weakEquivalences SSet.{v} (MixedDiagonalHom.map (𝟙 A) b) := by
  rw [right_comparison_eq]
  exact (weakEquivalences SSet.{v}).comp_mem _ _
    ((weakEquivalences SSet.{v}).of_isIso (rightIso A B).inv)
    ((weakEquivalences SSet.{v}).comp_mem _ _
      (BisimplicialModel.diagonal_map_weakEquivalence hcof hfib (rightComparison A b) hb)
      ((weakEquivalences SSet.{v}).of_isIso (rightIso A E).hom))

end SerrePositivity.HomotopyFunctionComplex.MixedDiagonalRows
