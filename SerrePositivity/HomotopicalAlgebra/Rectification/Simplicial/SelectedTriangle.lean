module

public import SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.RelativeChoiceBoundary

/-!
# 中断した任意モデル源への一般化：SelectedTriangle

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：Filling a triangle from its specified edges and endpoints。

## 方針（定義・証明）
全hornを用いたKan空間の高次ホモトピーの整合化に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0553][inventory]を参照する。

[inventory]: ../../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0553
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Filling a triangle from its specified edges and endpoints

Compatibility is derived from the six endpoint equations. The filler in
a fixed-boundary choice space retains all specified edges and keeps the
original boundary fixed throughout the whole triangle.
-/

@[expose] public section
universe v
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory HomotopicalAlgebra

namespace SerrePositivity.SimplicialModel.SelectedTriangle

structure Boundary (P : SSet.{v}) where
  vertex0 : SSet.stdSimplex.{v}.obj (SimplexCategory.mk 0) ⟶ P
  vertex1 : SSet.stdSimplex.{v}.obj (SimplexCategory.mk 0) ⟶ P
  vertex2 : SSet.stdSimplex.{v}.obj (SimplexCategory.mk 0) ⟶ P
  edge01 : SSet.stdSimplex.{v}.obj (SimplexCategory.mk 1) ⟶ P
  edge12 : SSet.stdSimplex.{v}.obj (SimplexCategory.mk 1) ⟶ P
  edge02 : SSet.stdSimplex.{v}.obj (SimplexCategory.mk 1) ⟶ P
  edge01_zero : SSet.stdSimplex.δ (1 : Fin 2) ≫ edge01 = vertex0
  edge01_one : SSet.stdSimplex.δ (0 : Fin 2) ≫ edge01 = vertex1
  edge12_zero : SSet.stdSimplex.δ (1 : Fin 2) ≫ edge12 = vertex1
  edge12_one : SSet.stdSimplex.δ (0 : Fin 2) ≫ edge12 = vertex2
  edge02_zero : SSet.stdSimplex.δ (1 : Fin 2) ≫ edge02 = vertex0
  edge02_one : SSet.stdSimplex.δ (0 : Fin 2) ≫ edge02 = vertex2

abbrev Boundary.faces {P : SSet.{v}} (d : Boundary P) :
    Fin 3 → (SSet.stdSimplex.{v}.obj (SimplexCategory.mk 1) ⟶ P) :=
  ![d.edge12, d.edge02, d.edge01]

lemma Boundary.compatible {P : SSet.{v}} (d : Boundary P) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.BoundaryGluing.StandardCompatible d.faces := by
  intro j k hjk
  fin_cases j <;> fin_cases k <;> norm_num at hjk
  · exact d.edge12_one.trans d.edge02_one.symm
  · exact d.edge12_zero.trans d.edge01_one.symm
  · exact d.edge02_zero.trans d.edge01_zero.symm

variable [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)

def fill {V T P : SSet.{v}} (i : V ⟶ T) [Mono i] (b : V ⟶ P)
    (p : P ⟶ SSet.stdSimplex.{v}.obj (SimplexCategory.mk 0))
    (hp : trivialFibrations SSet.{v} p) (d : Boundary (RelativeChoiceSpace.obj i b)) :
    SSet.stdSimplex.{v}.obj (SimplexCategory.mk 2) ⟶ RelativeChoiceSpace.obj i b :=
  (RelativeChoiceSpace.fill_standard_faces hcof hfib i b p hp 0 d.faces d.compatible).choose

@[reassoc (attr := simp)]
lemma fill_face {V T P : SSet.{v}} (i : V ⟶ T) [Mono i] (b : V ⟶ P)
    (p : P ⟶ SSet.stdSimplex.{v}.obj (SimplexCategory.mk 0))
    (hp : trivialFibrations SSet.{v} p) (d : Boundary (RelativeChoiceSpace.obj i b)) (k : Fin 3) :
    SSet.stdSimplex.δ k ≫ fill hcof hfib i b p hp d = d.faces k :=
  (RelativeChoiceSpace.fill_standard_faces hcof hfib i b p hp 0
    d.faces d.compatible).choose_spec.1 k

lemma fill_fixed_boundary {V T P : SSet.{v}} (i : V ⟶ T) [Mono i] (b : V ⟶ P)
    (p : P ⟶ SSet.stdSimplex.{v}.obj (SimplexCategory.mk 0))
    (hp : trivialFibrations SSet.{v} p) (d : Boundary (RelativeChoiceSpace.obj i b)) :
    i ▷ SSet.stdSimplex.{v}.obj (SimplexCategory.mk 2) ≫
        RelativeChoiceSpace.family i b (fill hcof hfib i b p hp d) =
      V ◁ (SSet.stdSimplex.isTerminalObj₀.from _ ≫ RelativeChoiceSpace.pointUnitIso.hom) ≫
        (ρ_ V).hom ≫ b :=
  (RelativeChoiceSpace.fill_standard_faces hcof hfib i b p hp 0 d.faces d.compatible).choose_spec.2

end SerrePositivity.SimplicialModel.SelectedTriangle
