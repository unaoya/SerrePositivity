module

public import SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.SelectedTriangle

/-!
# 中断した任意モデル源への一般化：SelectedLoopContraction

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：Contracting a selected loop without replacing its edge。

## 方針（定義・証明）
frameによる導来写像空間と整合図式の厳密化に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0552][inventory]を参照する。

[inventory]: ../../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0552
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Contracting a selected loop without replacing its edge

One side of the triangle is the specified loop. The other two sides are
the actual standard degeneracy of its vertex. Filling in a relative choice
space keeps its original fixed boundary throughout the contraction.
-/

@[expose] public section
universe v
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory HomotopicalAlgebra

namespace SerrePositivity.SimplicialModel.SelectedLoopContraction

abbrev degenerate {P : SSet.{v}}
    (a : SSet.stdSimplex.{v}.obj (SimplexCategory.mk 0) ⟶ P) :
    SSet.stdSimplex.{v}.obj (SimplexCategory.mk 1) ⟶ P :=
  SSet.stdSimplex.map (SimplexCategory.σ (0 : Fin 1)) ≫ a

lemma degenerate_vertex {P : SSet.{v}}
    (a : SSet.stdSimplex.{v}.obj (SimplexCategory.mk 0) ⟶ P) (i : Fin 2) :
    SSet.stdSimplex.δ i ≫ degenerate a = a := by
  have h : SSet.stdSimplex.δ i ≫ SSet.stdSimplex.map (SimplexCategory.σ (0 : Fin 1)) = 𝟙 _ :=
    SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun k => k ≫ a) h).trans (Category.id_comp _))

def data {P : SSet.{v}} (a : SSet.stdSimplex.{v}.obj (SimplexCategory.mk 0) ⟶ P)
    (e : SSet.stdSimplex.{v}.obj (SimplexCategory.mk 1) ⟶ P)
    (h₀ : SSet.stdSimplex.δ (1 : Fin 2) ≫ e = a)
    (h₁ : SSet.stdSimplex.δ (0 : Fin 2) ≫ e = a) : SelectedTriangle.Boundary P where
  vertex0 := a
  vertex1 := a
  vertex2 := a
  edge01 := e
  edge12 := degenerate a
  edge02 := degenerate a
  edge01_zero := h₀
  edge01_one := h₁
  edge12_zero := degenerate_vertex a 1
  edge12_one := degenerate_vertex a 0
  edge02_zero := degenerate_vertex a 1
  edge02_one := degenerate_vertex a 0

variable [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)

def fill {V T P : SSet.{v}} (i : V ⟶ T) [Mono i] (b : V ⟶ P)
    (p : P ⟶ SSet.stdSimplex.{v}.obj (SimplexCategory.mk 0))
    (hp : trivialFibrations SSet.{v} p)
    (a : SSet.stdSimplex.{v}.obj (SimplexCategory.mk 0) ⟶ RelativeChoiceSpace.obj i b)
    (e : SSet.stdSimplex.{v}.obj (SimplexCategory.mk 1) ⟶ RelativeChoiceSpace.obj i b)
    (h₀ : SSet.stdSimplex.δ (1 : Fin 2) ≫ e = a)
    (h₁ : SSet.stdSimplex.δ (0 : Fin 2) ≫ e = a) :=
  SelectedTriangle.fill hcof hfib i b p hp (data a e h₀ h₁)

lemma fill_face {V T P : SSet.{v}} (i : V ⟶ T) [Mono i] (b : V ⟶ P)
    (p : P ⟶ SSet.stdSimplex.{v}.obj (SimplexCategory.mk 0))
    (hp : trivialFibrations SSet.{v} p)
    (a : SSet.stdSimplex.{v}.obj (SimplexCategory.mk 0) ⟶ RelativeChoiceSpace.obj i b)
    (e : SSet.stdSimplex.{v}.obj (SimplexCategory.mk 1) ⟶ RelativeChoiceSpace.obj i b)
    (h₀ : SSet.stdSimplex.δ (1 : Fin 2) ≫ e = a)
    (h₁ : SSet.stdSimplex.δ (0 : Fin 2) ≫ e = a) (k : Fin 3) :
    SSet.stdSimplex.δ k ≫ fill hcof hfib i b p hp a e h₀ h₁ = (data a e h₀ h₁).faces k :=
  SelectedTriangle.fill_face hcof hfib i b p hp _ k

end SerrePositivity.SimplicialModel.SelectedLoopContraction
