module

public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.FrameSquareComparison
public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.ResolutionBarConeDiagram

/-!
# 中断した任意モデル源への一般化：ResolutionBarFrameSquares

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：Derived frame comparisons for the actual global bar cone squares。

## 方針（定義・証明）
frameによる導来写像空間と整合図式の厳密化に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0292][inventory]を参照する。

[inventory]: ../../../../formalization-plans/k-theory-generalization-inventory.md#m0292
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Derived frame comparisons for the actual global bar cone squares

The prefix uses its original framed morphism. The source row operator and
both vertical maps are lifted individually. Their original frame composites
are retained as points; no equality or functoriality of these lifts is assumed.
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory HomotopicalAlgebra Opposite
open SerrePositivity.SimplicialModel

namespace SerrePositivity.HomotopyFunctionComplex.ResolutionBarFrameSquares
variable {C : Type u} [Category.{v} C] [ModelCategory C]
  (R : RightResolutionMapping.Index C)
local instance : ModelCategory (SimplexCategory ⥤ C) := Reedy.simplexModelCategory C
local instance : ModelCategory (SimplexCategory ⥤ Cᵒᵖ) := Reedy.simplexModelCategory Cᵒᵖ

def leftSource (s : ResolutionBarConeDiagram.Index R) : FramedResolution C :=
  FramedResolution.ofResolution ((ResolutionBarConeDiagram.leftSource R).obj s)
def leftTarget (s : ResolutionBarConeDiagram.Index R) : FramedResolution C :=
  (SerrePositivity.NerveSimplexStart.start ((ResolutionBarConeDiagram.indices R).obj s)).left.1.unop

def leftSourceMap {s t : ResolutionBarConeDiagram.Index R} (f : s ⟶ t) :
    leftSource R s ⟶ leftSource R t :=
  FramedResolution.lift ((ResolutionBarConeDiagram.leftSource R).map f)
def leftTargetMap {s t : ResolutionBarConeDiagram.Index R} (f : s ⟶ t) :
    leftTarget R s ⟶ leftTarget R t :=
  (SerrePositivity.NerveSimplexStart.startMap
    ((ResolutionBarConeDiagram.indices R).map f)).left.1.unop

variable (a : NerveFirstChoice.System (ResolutionBarCenters.leftChoices R))

def leftCone (s : ResolutionBarConeDiagram.Index R) : leftSource R s ⟶ leftTarget R s :=
  FramedResolution.lift ((ResolutionBarConeDiagram.left R a).app s)

lemma left_inner_square {s t : ResolutionBarConeDiagram.Index R} (f : s ⟶ t) :
    (leftSourceMap R f ≫ leftCone R a t).map =
      (leftCone R a s ≫ leftTargetMap R f).map :=
  (ResolutionBarConeDiagram.left R a).naturality f

abbrev leftSpace {s t : ResolutionBarConeDiagram.Index R} (f : s ⟶ t) : SSet.{v} :=
  FrameSquareComparison.obj (leftSourceMap R f) (leftCone R a t)
abbrev leftStart {s t : ResolutionBarConeDiagram.Index R} (f : s ⟶ t) :
    SSet.stdSimplex.{v}.obj (SimplexCategory.mk 0) ⟶ leftSpace R a f :=
  FrameSquareComparison.leftPoint (leftSourceMap R f) (leftCone R a t)
abbrev leftFinish {s t : ResolutionBarConeDiagram.Index R} (f : s ⟶ t) :
    SSet.stdSimplex.{v}.obj (SimplexCategory.mk 0) ⟶ leftSpace R a f :=
  FrameSquareComparison.rightPoint (leftSourceMap R f) (leftCone R a t)
    (leftCone R a s) (leftTargetMap R f) (left_inner_square R a f)

lemma left_recovery (n : SimplexCategoryᵒᵖ) (c : (ResolutionBarEvaluation.bar R).obj n) :
    leftCone R a (op ((ResolutionBarEvaluation.bar R).elementsMk n c)) =
      (FramedResolution.lift (ResolutionBarSimplexCone.left R a n c) :
        FramedResolution.ofResolution (ResolutionFrameRows.row R.1.unop.inner n.unop) ⟶
          (c.obj 0).left.obj.1.unop) := rfl

def rightSource (s : ResolutionBarConeDiagram.Index R) : FramedResolution Cᵒᵖ :=
  FramedResolution.ofResolution ((ResolutionBarConeDiagram.rightSource R).obj s)
def rightTarget (s : ResolutionBarConeDiagram.Index R) : FramedResolution Cᵒᵖ :=
  (SerrePositivity.NerveSimplexStart.start ((ResolutionBarConeDiagram.indices R).obj s)).left.2.unop

def rightSourceMap {s t : ResolutionBarConeDiagram.Index R} (f : s ⟶ t) :
    rightSource R s ⟶ rightSource R t :=
  FramedResolution.lift ((ResolutionBarConeDiagram.rightSource R).map f)
def rightTargetMap {s t : ResolutionBarConeDiagram.Index R} (f : s ⟶ t) :
    rightTarget R s ⟶ rightTarget R t :=
  (SerrePositivity.NerveSimplexStart.startMap
    ((ResolutionBarConeDiagram.indices R).map f)).left.2.unop

variable (b : NerveFirstChoice.System (ResolutionBarCenters.rightChoices R))

def rightCone (s : ResolutionBarConeDiagram.Index R) : rightSource R s ⟶ rightTarget R s :=
  FramedResolution.lift ((ResolutionBarConeDiagram.right R b).app s)

lemma right_inner_square {s t : ResolutionBarConeDiagram.Index R} (f : s ⟶ t) :
    (rightSourceMap R f ≫ rightCone R b t).map =
      (rightCone R b s ≫ rightTargetMap R f).map :=
  (ResolutionBarConeDiagram.right R b).naturality f

abbrev rightSpace {s t : ResolutionBarConeDiagram.Index R} (f : s ⟶ t) : SSet.{v} :=
  FrameSquareComparison.obj (rightSourceMap R f) (rightCone R b t)
abbrev rightStart {s t : ResolutionBarConeDiagram.Index R} (f : s ⟶ t) :
    SSet.stdSimplex.{v}.obj (SimplexCategory.mk 0) ⟶ rightSpace R b f :=
  FrameSquareComparison.leftPoint (rightSourceMap R f) (rightCone R b t)
abbrev rightFinish {s t : ResolutionBarConeDiagram.Index R} (f : s ⟶ t) :
    SSet.stdSimplex.{v}.obj (SimplexCategory.mk 0) ⟶ rightSpace R b f :=
  FrameSquareComparison.rightPoint (rightSourceMap R f) (rightCone R b t)
    (rightCone R b s) (rightTargetMap R f) (right_inner_square R b f)

lemma right_recovery (n : SimplexCategoryᵒᵖ) (c : (ResolutionBarEvaluation.bar R).obj n) :
    rightCone R b (op ((ResolutionBarEvaluation.bar R).elementsMk n c)) =
      (FramedResolution.lift (ResolutionBarSimplexCone.right R b n c) :
        FramedResolution.ofResolution (ResolutionFrameRows.row R.2.unop.inner n.unop) ⟶
          (c.obj 0).left.obj.2.unop) := rfl

variable [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)

include hcof in
lemma left_interval {s t : ResolutionBarConeDiagram.Index R} (f : s ⟶ t) :
    ∃ e : SSet.stdSimplex.{v}.obj (SimplexCategory.mk 1) ⟶ leftSpace R a f,
      SSet.stdSimplex.map (SimplexCategory.δ (1 : Fin 2)) ≫ e = leftStart R a f ∧
      SSet.stdSimplex.map (SimplexCategory.δ (0 : Fin 2)) ≫ e = leftFinish R a f :=
  FrameSquareComparison.interval _ _ _ _ (left_inner_square R a f) hcof

include hcof in
lemma left_extension {s t : ResolutionBarConeDiagram.Index R} (f : s ⟶ t)
    {K L : SSet.{v}} (i : K ⟶ L) [Mono i] (boundary : K ⟶ leftSpace R a f) :
    ∃ e : L ⟶ leftSpace R a f, i ≫ e = boundary :=
  FrameSquareComparison.extension _ _ hcof i boundary

include hcof in
lemma right_interval {s t : ResolutionBarConeDiagram.Index R} (f : s ⟶ t) :
    ∃ e : SSet.stdSimplex.{v}.obj (SimplexCategory.mk 1) ⟶ rightSpace R b f,
      SSet.stdSimplex.map (SimplexCategory.δ (1 : Fin 2)) ≫ e = rightStart R b f ∧
      SSet.stdSimplex.map (SimplexCategory.δ (0 : Fin 2)) ≫ e = rightFinish R b f :=
  FrameSquareComparison.interval _ _ _ _ (right_inner_square R b f) hcof

include hcof in
lemma right_extension {s t : ResolutionBarConeDiagram.Index R} (f : s ⟶ t)
    {K L : SSet.{v}} (i : K ⟶ L) [Mono i] (boundary : K ⟶ rightSpace R b f) :
    ∃ e : L ⟶ rightSpace R b f, i ≫ e = boundary :=
  FrameSquareComparison.extension _ _ hcof i boundary

include hcof in
lemma pair_extension {s t : ResolutionBarConeDiagram.Index R} (f : s ⟶ t)
    {K L : SSet.{v}} (i : K ⟶ L) [Mono i]
    (boundaryLeft : K ⟶ leftSpace R a f) (boundaryRight : K ⟶ rightSpace R b f) :
    ∃ (eLeft : L ⟶ leftSpace R a f) (eRight : L ⟶ rightSpace R b f),
      i ≫ eLeft = boundaryLeft ∧ i ≫ eRight = boundaryRight := by
  obtain ⟨eLeft, hLeft⟩ := left_extension R a hcof f i boundaryLeft
  obtain ⟨eRight, hRight⟩ := right_extension R b hcof f i boundaryRight
  exact ⟨eLeft, eRight, hLeft, hRight⟩

end SerrePositivity.HomotopyFunctionComplex.ResolutionBarFrameSquares
