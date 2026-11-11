module

public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.CoherentLiftRelative
public import SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.RelativeChoiceMaps

/-!
# 中断した任意モデル源への一般化：CoherentLiftEdges

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：Selected relative composition edges with exact endpoints。

## 方針（定義・証明）
全hornを用いたKan空間の高次ホモトピーの整合化に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0065][inventory]を参照する。

[inventory]: ../../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0065
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Selected relative composition edges with exact endpoints

The interval parameters live in the actual relative choice spaces. Keeping
these parameters, rather than only their evaluated homotopies, allows
transport and gluing with their already specified endpoints retained.
No unit or associativity law for these independent choices is asserted.
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SerrePositivity.SimplicialModel

namespace SerrePositivity.HomotopyFunctionComplex.CoherentLiftRelative
variable {C : Type u} [Category.{v} C] [ModelCategory C] [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)

abbrev postLeftPoint (X Y W : ResolutionObject C) (f : X.base ⟶ Y.base) (g : Y ⟶ W) :=
  RelativeChoiceSpace.ofExtension (vertexInclusion X Y f) (postBoundary X Y W f g)
    (postLeft hcof X Y W f g) (postLeft_vertices hcof X Y W f g)

abbrev postRightPoint (X Y W : ResolutionObject C) (f : X.base ⟶ Y.base) (g : Y ⟶ W) :=
  RelativeChoiceSpace.ofExtension (vertexInclusion X Y f) (postBoundary X Y W f g)
    (postRight hcof X Y W f g) (postRight_vertices hcof X Y W f g)

def postEdge (X Y W : ResolutionObject C) (f : X.base ⟶ Y.base) (g : Y ⟶ W) :
    SSet.stdSimplex.{v}.obj (SimplexCategory.mk 1) ⟶ postChoiceSpace X Y W f g :=
  (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.interval hcof hfib _ _ (ResolutionLiftSpace.projection X W (f ≫ g.base))
    (ResolutionLiftSpace.projection_trivialFibration hcof X W (f ≫ g.base))
    (postLeftPoint hcof X Y W f g) (postRightPoint hcof X Y W f g)).choose

@[reassoc (attr := simp)]
lemma postEdge_at_zero (X Y W : ResolutionObject C) (f : X.base ⟶ Y.base) (g : Y ⟶ W) :
    SSet.stdSimplex.δ (1 : Fin 2) ≫ postEdge hcof hfib X Y W f g = postLeftPoint hcof X Y W f g :=
  (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.interval hcof hfib _ _ (ResolutionLiftSpace.projection X W (f ≫ g.base))
    (ResolutionLiftSpace.projection_trivialFibration hcof X W (f ≫ g.base))
    (postLeftPoint hcof X Y W f g) (postRightPoint hcof X Y W f g)).choose_spec.1

@[reassoc (attr := simp)]
lemma postEdge_at_one (X Y W : ResolutionObject C) (f : X.base ⟶ Y.base) (g : Y ⟶ W) :
    SSet.stdSimplex.δ (0 : Fin 2) ≫ postEdge hcof hfib X Y W f g = postRightPoint hcof X Y W f g :=
  (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.interval hcof hfib _ _ (ResolutionLiftSpace.projection X W (f ≫ g.base))
    (ResolutionLiftSpace.projection_trivialFibration hcof X W (f ≫ g.base))
    (postLeftPoint hcof X Y W f g) (postRightPoint hcof X Y W f g)).choose_spec.2

abbrev preLeftPoint (X Y W : ResolutionObject C) (f : X ⟶ Y) (g : Y.base ⟶ W.base)
    (φ : ResolutionLiftPrecomposition.FrameMap f) :=
  RelativeChoiceSpace.ofExtension (vertexInclusion Y W g) (preBoundary X Y W f g)
    (preLeft hcof X Y W f g φ) (preLeft_vertices hcof X Y W f g φ)

abbrev preRightPoint (X Y W : ResolutionObject C) (f : X ⟶ Y) (g : Y.base ⟶ W.base) :=
  RelativeChoiceSpace.ofExtension (vertexInclusion Y W g) (preBoundary X Y W f g)
    (preRight hcof X Y W f g) (preRight_vertices hcof X Y W f g)

def preEdge (X Y W : ResolutionObject C) (f : X ⟶ Y) (g : Y.base ⟶ W.base)
    (φ : ResolutionLiftPrecomposition.FrameMap f) :
    SSet.stdSimplex.{v}.obj (SimplexCategory.mk 1) ⟶ preChoiceSpace X Y W f g :=
  (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.interval hcof hfib _ _ (ResolutionLiftSpace.projection X W (f.base ≫ g))
    (ResolutionLiftSpace.projection_trivialFibration hcof X W (f.base ≫ g))
    (preLeftPoint hcof X Y W f g φ) (preRightPoint hcof X Y W f g)).choose

@[reassoc (attr := simp)]
lemma preEdge_at_zero (X Y W : ResolutionObject C) (f : X ⟶ Y) (g : Y.base ⟶ W.base)
    (φ : ResolutionLiftPrecomposition.FrameMap f) :
    SSet.stdSimplex.δ (1 : Fin 2) ≫ preEdge hcof hfib X Y W f g φ =
      preLeftPoint hcof X Y W f g φ :=
  (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.interval hcof hfib _ _ (ResolutionLiftSpace.projection X W (f.base ≫ g))
    (ResolutionLiftSpace.projection_trivialFibration hcof X W (f.base ≫ g))
    (preLeftPoint hcof X Y W f g φ) (preRightPoint hcof X Y W f g)).choose_spec.1

@[reassoc (attr := simp)]
lemma preEdge_at_one (X Y W : ResolutionObject C) (f : X ⟶ Y) (g : Y.base ⟶ W.base)
    (φ : ResolutionLiftPrecomposition.FrameMap f) :
    SSet.stdSimplex.δ (0 : Fin 2) ≫ preEdge hcof hfib X Y W f g φ =
      preRightPoint hcof X Y W f g :=
  (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.interval hcof hfib _ _ (ResolutionLiftSpace.projection X W (f.base ≫ g))
    (ResolutionLiftSpace.projection_trivialFibration hcof X W (f.base ≫ g))
    (preLeftPoint hcof X Y W f g φ) (preRightPoint hcof X Y W f g)).choose_spec.2

end SerrePositivity.HomotopyFunctionComplex.CoherentLiftRelative
