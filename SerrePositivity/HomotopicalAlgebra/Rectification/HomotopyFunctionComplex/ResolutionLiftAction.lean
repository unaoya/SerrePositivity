module

public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.ResolutionLiftSpace
public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.LiftSpaceAction
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.DiagonalMappingRows

/-!
# 中断した任意モデル源への一般化：ResolutionLiftAction

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：Resolution lift spaces act on the actual diagonal Hom。

## 方針（定義・証明）
frameによる導来写像空間と整合図式の厳密化に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0305][inventory]を参照する。

[inventory]: ../../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0305
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Resolution lift spaces act on the actual diagonal Hom

The action retains higher simplices of the lift space. Prescribed boundary
actions extend with the chosen lift fillers. Comparison with ordinary
resolution Hom is an actual map; its weak equivalence is a separate theorem,
not an input or assertion of this module.
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra

namespace SerrePositivity.HomotopyFunctionComplex.ResolutionLiftAction
variable {C : Type u} [Category.{v} C] [ModelCategory C]
local instance : ModelCategory (SimplexCategory ⥤ C) := Reedy.simplexModelCategory C

abbrev target (X : ResolutionObject C) (Z : C) : SSet.{v} :=
  (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom (DiagonalFrame.obj (ResolutionLiftSpace.frame X).obj)).obj Z

/-- The concrete comparison induced by the diagonal augmentation. -/
abbrev comparison (X : ResolutionObject C) (Z : C) :
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom X.resolution.obj).obj Z ⟶ target X Z :=
  (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHomMap (DiagonalFrame.augmentation (ResolutionLiftSpace.frame X).augmentation)).app Z

/-- Actual action with an arbitrary simplicial parameter T. -/
abbrev parameterized (X Y : ResolutionObject C) (f : X.base ⟶ Y.base) (Z : C)
    {T : SSet.{v}} (s : T ⟶ ResolutionLiftSpace.obj X Y f)
    (t : T ⟶ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom Y.resolution.obj).obj Z) : T ⟶ target X Z :=
  LiftSpaceAction.parameterized (ResolutionLiftSpace.frame X).obj
    (ResolutionLiftSpace.frame X).augmentation Y.resolution.augmentation
    (ResolutionLiftSpace.baseMap X Y f) Z s t

abbrev action (X Y : ResolutionObject C) (f : X.base ⟶ Y.base) (Z : C) :
    ResolutionLiftSpace.obj X Y f ⨯ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom Y.resolution.obj).obj Z ⟶ target X Z :=
  parameterized X Y f Z prod.fst prod.snd

/-- At a strict lift, the action agrees with the original Hom map and comparison. -/
lemma ofLift {X Y : ResolutionObject C} (f : X ⟶ Y) (Z : C) {T : SSet.{v}}
    (d : T ⟶ SSet.stdSimplex.{v}.obj (SimplexCategory.mk 0))
    (t : T ⟶ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom Y.resolution.obj).obj Z) :
    parameterized X Y f.base Z (d ≫ ResolutionLiftSpace.ofLift f) t =
      t ≫ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHomMap f.diagram).app Z ≫ comparison X Z := by
  refine (LiftSpaceAction.ofLift _ _ _ _ Z d f.diagram f.over t).trans ?_
  ext n x
  change (((DiagonalFrame.augmentation (ResolutionLiftSpace.frame X).augmentation).app n.unop) ≫
      f.diagram.app n.unop) ≫ t.app n x =
    (DiagonalFrame.augmentation (ResolutionLiftSpace.frame X).augmentation).app n.unop ≫
      (f.diagram.app n.unop ≫ t.app n x)
  exact Category.assoc _ _ _

@[reassoc]
lemma naturality (X Y : ResolutionObject C) (f : X.base ⟶ Y.base) (Z : C)
    {T U : SSet.{v}} (u : U ⟶ T) (s : T ⟶ ResolutionLiftSpace.obj X Y f)
    (t : T ⟶ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom Y.resolution.obj).obj Z) :
    u ≫ parameterized X Y f Z s t = parameterized X Y f Z (u ≫ s) (u ≫ t) :=
  LiftSpaceAction.parameterized_naturality _ _ _ _ Z u s t

lemma target_naturality (X Y : ResolutionObject C) (f : X.base ⟶ Y.base)
    {Z Z' : C} (h : Z ⟶ Z') {T : SSet.{v}} (s : T ⟶ ResolutionLiftSpace.obj X Y f)
    (t : T ⟶ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom Y.resolution.obj).obj Z) :
    parameterized X Y f Z' s (t ≫ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom Y.resolution.obj).map h) =
      parameterized X Y f Z s t ≫
        (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom (DiagonalFrame.obj (ResolutionLiftSpace.frame X).obj)).map h :=
  DiagonalHom.pairing_target_naturality _ _ Z h _ _

/-- The augmented bisimplicial comparison, before passing to its diagonal. -/
abbrev rowComparison (X : ResolutionObject C) (Z : C) :=
  DiagonalMappingRows.comparison (ResolutionLiftSpace.frame X).augmentation Z

lemma row_kanComplex (X : ResolutionObject C) (Z : C) [IsFibrant Z]
    (n : SimplexCategoryᵒᵖ) :
    SSet.KanComplex ((DiagonalMappingRows.obj (ResolutionLiftSpace.frame X).obj Z).obj n) :=
  DiagonalMappingRows.row_kanComplex (ResolutionLiftSpace.frame X)
    X.resolution.homotopicallyConstant n Z

variable [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)

include hcof in
lemma rowComparison_weakEquivalence (X : ResolutionObject C) (Z : C) [IsFibrant Z]
    (n : SimplexCategoryᵒᵖ) :
    weakEquivalences SSet.{v} ((rowComparison X Z).app n) :=
  DiagonalMappingRows.comparison_weakEquivalence (ResolutionLiftSpace.frame X)
    hcof X.resolution.cofibrant Z n

include hcof in
/-- Arbitrary compatible lift boundaries extend while preserving their actual action. -/
lemma extends_action (X Y : ResolutionObject C) (f : X.base ⟶ Y.base) (Z : C)
    {K L : SSet.{v}} (i : K ⟶ L) [Mono i] (b : K ⟶ ResolutionLiftSpace.obj X Y f)
    (t : L ⟶ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom Y.resolution.obj).obj Z) :
    ∃ e : L ⟶ ResolutionLiftSpace.obj X Y f, i ≫ e = b ∧
      i ≫ parameterized X Y f Z e t = parameterized X Y f Z b (i ≫ t) := by
  obtain ⟨e, he⟩ := ResolutionLiftSpace.extension hcof X Y f i b
  exact ⟨e, he, (naturality X Y f Z i e t).trans (congrArg
    (fun s => parameterized X Y f Z s (i ≫ t)) he)⟩

end SerrePositivity.HomotopyFunctionComplex.ResolutionLiftAction
