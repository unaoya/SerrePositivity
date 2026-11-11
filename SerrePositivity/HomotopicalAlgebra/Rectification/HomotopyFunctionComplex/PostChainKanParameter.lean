module

public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.PostCompositionChain
public import SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.RelativeChoiceCells

/-!
# 中断した任意モデル源への一般化：PostChainKanParameter

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：A Kan parameter retaining all selected cut triangles of a finite chain。

## 方針（定義・証明）
bar型の鎖パラメータと整合図式の厳密化に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0257][inventory]を参照する。

[inventory]: ../../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0257
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# A Kan parameter retaining all selected cut triangles of a finite chain

The value-side replacement unit is a monomorphism. The skeletal assembly
extends the whole glued family along it, retaining all selected triangles
and their common direct edge. No replacement of source objects is assumed.
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory HomotopicalAlgebra
open SerrePositivity.SimplicialModel
open SerrePositivity.HomotopyFunctionComplex.CoherentLiftRelative

namespace SerrePositivity.HomotopyFunctionComplex.PostChainKanParameter
variable {C : Type u} [Category.{v} C] [ModelCategory C] [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
  {n : ℕ} (F : Fin (n + 1) ⥤ ResolutionObject C)
  (X : ResolutionObject C) (f : X.base ⟶ (F.obj 0).base)

abbrev parameter : SSet.{v} :=
  (KanReplacement.functor hcof hfib).obj (PostCompositionChain.parameter F)

abbrev inclusion : PostCompositionChain.parameter F ⟶ parameter hcof hfib F :=
  (KanReplacement.unit hcof hfib).app (PostCompositionChain.parameter F)

local instance : Mono (inclusion hcof hfib F) :=
  KanReplacement.unit_mono hcof hfib _

lemma parameter_kanComplex : SSet.KanComplex (parameter hcof hfib F) :=
  KanReplacement.kanComplex hcof hfib _

def comparison : parameter hcof hfib F ⟶ PostCompositionChain.choiceSpace F X f :=
  RelativeChoiceCells.assemble hcof hfib (vertexInclusion X (PostCompositionChain.first F) f)
    (postBoundary X (PostCompositionChain.first F) (PostCompositionChain.last F) f
      (PostCompositionChain.total F))
    (ResolutionLiftSpace.projection X (PostCompositionChain.last F)
      (f ≫ (PostCompositionChain.total F).base))
    (ResolutionLiftSpace.projection_trivialFibration hcof X (PostCompositionChain.last F)
      (f ≫ (PostCompositionChain.total F).base))
    (inclusion hcof hfib F) (PostCompositionChain.comparison hcof hfib F X f) (fun _ _ => none)

@[reassoc]
lemma comparison_initial : inclusion hcof hfib F ≫ comparison hcof hfib F X f =
    PostCompositionChain.comparison hcof hfib F X f :=
  RelativeChoiceCells.assemble_initial _ _ _ _ _ _ _ _ _

abbrev cut (i : Fin (n + 1)) :
    SSet.stdSimplex.{v}.obj (SimplexCategory.mk 2) ⟶ parameter hcof hfib F :=
  _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.TriangleBook.triangle (ULift.{v} (Fin (n + 1))) ⟨i⟩ ≫ inclusion hcof hfib F

@[reassoc]
lemma comparison_cut (i : Fin (n + 1)) :
    cut hcof hfib F i ≫ comparison hcof hfib F X f =
      PostCompositionChain.cutTriangle hcof hfib F X f i := by
  rw [cut, Category.assoc, comparison_initial, PostCompositionChain.comparison_cut]

@[reassoc]
lemma comparison_direct :
    (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.TriangleBook.sharedEdge (ULift.{v} (Fin (n + 1))) ≫ inclusion hcof hfib F) ≫
      comparison hcof hfib F X f = postEdge hcof hfib X (PostCompositionChain.first F)
        (PostCompositionChain.last F) f (PostCompositionChain.total F) := by
  rw [Category.assoc, comparison_initial, PostCompositionChain.comparison_direct]

lemma fixed_boundary :
    vertexInclusion X (PostCompositionChain.first F) f ▷ parameter hcof hfib F ≫
      RelativeChoiceSpace.family (vertexInclusion X (PostCompositionChain.first F) f)
        (postBoundary X (PostCompositionChain.first F) (PostCompositionChain.last F) f
          (PostCompositionChain.total F)) (comparison hcof hfib F X f) =
      vertices X (PostCompositionChain.first F) f ◁ (SSet.stdSimplex.isTerminalObj₀.from _ ≫
        RelativeChoiceSpace.pointUnitIso.hom) ≫ (ρ_ _).hom ≫
          postBoundary X (PostCompositionChain.first F) (PostCompositionChain.last F) f
            (PostCompositionChain.total F) :=
  RelativeChoiceSpace.family_fixed_boundary _ _ _

lemma action_cut (i : Fin (n + 1)) (Z : C)
    (t : CoherentLiftTuples.obj X (PostCompositionChain.first F) f ⊗ parameter hcof hfib F ⟶
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom (PostCompositionChain.last F).resolution.obj).obj Z) :
    CoherentLiftTuples.obj X (PostCompositionChain.first F) f ◁ cut hcof hfib F i ≫
      KanLiftAction.parameterized hcof hfib X (PostCompositionChain.last F)
        (f ≫ (PostCompositionChain.total F).base) Z
        (RelativeChoiceSpace.family (vertexInclusion X (PostCompositionChain.first F) f)
          (postBoundary X (PostCompositionChain.first F) (PostCompositionChain.last F) f
            (PostCompositionChain.total F)) (comparison hcof hfib F X f)) t =
      KanLiftAction.parameterized hcof hfib X (PostCompositionChain.last F)
        (f ≫ (PostCompositionChain.total F).base) Z
        (RelativeChoiceSpace.family (vertexInclusion X (PostCompositionChain.first F) f)
          (postBoundary X (PostCompositionChain.first F) (PostCompositionChain.last F) f
            (PostCompositionChain.total F)) (PostCompositionChain.cutTriangle hcof hfib F X f i))
        ((CoherentLiftTuples.obj X (PostCompositionChain.first F) f ◁ cut hcof hfib F i) ≫ t) := by
  rw [KanLiftAction.parameterized_naturality, ← RelativeChoiceSpace.family_naturality,
    comparison_cut]

end SerrePositivity.HomotopyFunctionComplex.PostChainKanParameter
