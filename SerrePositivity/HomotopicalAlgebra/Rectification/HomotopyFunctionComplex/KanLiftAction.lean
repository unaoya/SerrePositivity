module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.KanReplacement
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.DiagonalMappingWeakEquivalence
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.PiZero

/-!
# 中断した任意モデル源への一般化：KanLiftAction

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：Kan targets for higher resolution-lift actions。

## 方針（定義・証明）
frameによる導来写像空間と整合図式の厳密化に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0102][inventory]を参照する。

[inventory]: ../../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0102
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Kan targets for higher resolution-lift actions

The original actual mapping space is already Kan at a fibrant target.
Only the diagonal action target is replaced. Actions are postcomposed
with the value-side replacement unit; no product preservation of the
replacement functor is assumed.
-/

@[expose] public section
universe v u vH uH
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra

namespace SerrePositivity.HomotopyFunctionComplex.KanLiftAction
variable {C : Type u} [Category.{v} C] [ModelCategory C] [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)

local instance : ModelCategory (SimplexCategory ⥤ C) := Reedy.simplexModelCategory C

abbrev target (X : ResolutionObject C) (Z : C) : SSet.{v} :=
  (SimplicialModel.KanReplacement.functor hcof hfib).obj (ResolutionLiftAction.target X Z)

abbrev comparison (X : ResolutionObject C) (Z : C) :
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom X.resolution.obj).obj Z ⟶ target hcof hfib X Z :=
  ResolutionLiftAction.comparison X Z ≫
    (SimplicialModel.KanReplacement.unit hcof hfib).app (ResolutionLiftAction.target X Z)

/-- Target functoriality uses only the value-side replacement functor. -/
abbrev targetFunctor (X : ResolutionObject C) : C ⥤ SSet.{v} :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom (DiagonalFrame.obj (ResolutionLiftSpace.frame X).obj) ⋙
    SimplicialModel.KanReplacement.functor hcof hfib

/-- The original resolution Hom compares naturally with the Kan-valued functor. -/
def comparisonNatTrans (X : ResolutionObject C) :
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom X.resolution.obj ⟶ targetFunctor hcof hfib X where
  app Z := comparison hcof hfib X Z
  naturality {Z Z'} f := by
    have hr := (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHomMap
      (DiagonalFrame.augmentation (ResolutionLiftSpace.frame X).augmentation)).naturality f
    have hu := (SimplicialModel.KanReplacement.unit hcof hfib).naturality
      ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom (DiagonalFrame.obj (ResolutionLiftSpace.frame X).obj)).map f)
    change (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom (DiagonalFrame.obj (ResolutionLiftSpace.frame X).obj)).map f ≫
        (SimplicialModel.KanReplacement.unit hcof hfib).app (ResolutionLiftAction.target X Z') =
      (SimplicialModel.KanReplacement.unit hcof hfib).app (ResolutionLiftAction.target X Z) ≫
        (targetFunctor hcof hfib X).map f at hu
    change _ ≫ (ResolutionLiftAction.comparison X Z' ≫ _) =
      (ResolutionLiftAction.comparison X Z ≫ _) ≫ _
    rw [← Category.assoc, hr, Category.assoc, hu, ← Category.assoc]

lemma target_kanComplex (X : ResolutionObject C) (Z : C) :
    SSet.KanComplex (target hcof hfib X Z) := SimplicialModel.KanReplacement.kanComplex _ _ _

lemma comparison_weakEquivalence (X : ResolutionObject C) (Z : C) [IsFibrant Z] :
    weakEquivalences SSet.{v} (comparison hcof hfib X Z) :=
  (weakEquivalences SSet.{v}).comp_mem _ _
    (DiagonalMappingComparison.liftAction_comparison_weakEquivalence hcof hfib X Z)
    (SimplicialModel.KanReplacement.unit_weakEquivalence hcof hfib _)

lemma target_map_weakEquivalence (X : ResolutionObject C) {Z Z' : C}
    [IsFibrant Z] [IsFibrant Z'] (f : Z ⟶ Z') (hf : weakEquivalences C f) :
    weakEquivalences SSet.{v} ((targetFunctor hcof hfib X).map f) := by
  have : WeakEquivalence f := ⟨hf⟩
  have hw := cosimplicialHom_weakEquivalence_of_fibrant hcof
    X.resolution.obj X.resolution.cofibrant f
  have hc := (weakEquivalences SSet.{v}).comp_mem _ _ hw
    (comparison_weakEquivalence hcof hfib X Z')
  exact (weakEquivalences SSet.{v}).of_precomp _ _
    (comparison_weakEquivalence hcof hfib X Z)
    ((comparisonNatTrans hcof hfib X).naturality f ▸ hc)

/-- The same actual lift simplices act into a Kan target, without replacing products. -/
abbrev parameterized (X Y : ResolutionObject C) (f : X.base ⟶ Y.base) (Z : C)
    {T : SSet.{v}} (s : T ⟶ ResolutionLiftSpace.obj X Y f)
    (t : T ⟶ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom Y.resolution.obj).obj Z) : T ⟶ target hcof hfib X Z :=
  ResolutionLiftAction.parameterized X Y f Z s t ≫
    (SimplicialModel.KanReplacement.unit hcof hfib).app (ResolutionLiftAction.target X Z)

abbrev action (X Y : ResolutionObject C) (f : X.base ⟶ Y.base) (Z : C) :
    ResolutionLiftSpace.obj X Y f ⨯ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom Y.resolution.obj).obj Z ⟶
      target hcof hfib X Z :=
  parameterized hcof hfib X Y f Z prod.fst prod.snd

@[reassoc]
lemma parameterized_naturality (X Y : ResolutionObject C) (f : X.base ⟶ Y.base) (Z : C)
    {T U : SSet.{v}} (u : U ⟶ T) (s : T ⟶ ResolutionLiftSpace.obj X Y f)
    (t : T ⟶ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom Y.resolution.obj).obj Z) :
    u ≫ parameterized hcof hfib X Y f Z s t =
      parameterized hcof hfib X Y f Z (u ≫ s) (u ≫ t) := by
  rw [← Category.assoc, ResolutionLiftAction.naturality]

lemma parameterized_target_naturality (X Y : ResolutionObject C) (f : X.base ⟶ Y.base)
    {Z Z' : C} (h : Z ⟶ Z') {T : SSet.{v}} (s : T ⟶ ResolutionLiftSpace.obj X Y f)
    (t : T ⟶ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom Y.resolution.obj).obj Z) :
    parameterized hcof hfib X Y f Z' s (t ≫ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom Y.resolution.obj).map h) =
      parameterized hcof hfib X Y f Z s t ≫ (targetFunctor hcof hfib X).map h := by
  have hu := (SimplicialModel.KanReplacement.unit hcof hfib).naturality
    ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom (DiagonalFrame.obj (ResolutionLiftSpace.frame X).obj)).map h)
  change (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom (DiagonalFrame.obj (ResolutionLiftSpace.frame X).obj)).map h ≫
      (SimplicialModel.KanReplacement.unit hcof hfib).app (ResolutionLiftAction.target X Z') =
    (SimplicialModel.KanReplacement.unit hcof hfib).app (ResolutionLiftAction.target X Z) ≫
      (targetFunctor hcof hfib X).map h at hu
  change ResolutionLiftAction.parameterized X Y f Z' s
      (t ≫ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom Y.resolution.obj).map h) ≫ _ = (_ ≫ _) ≫ _
  rw [ResolutionLiftAction.target_naturality, Category.assoc, hu, ← Category.assoc]

lemma ofLift {X Y : ResolutionObject C} (f : X ⟶ Y) (Z : C) {T : SSet.{v}}
    (d : T ⟶ SSet.stdSimplex.{v}.obj (SimplexCategory.mk 0))
    (t : T ⟶ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom Y.resolution.obj).obj Z) :
    parameterized hcof hfib X Y f.base Z (d ≫ ResolutionLiftSpace.ofLift f) t =
      t ≫ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHomMap f.diagram).app Z ≫ comparison hcof hfib X Z := by
  exact (congrArg (fun k => k ≫
    (SimplicialModel.KanReplacement.unit hcof hfib).app (ResolutionLiftAction.target X Z))
    (ResolutionLiftAction.ofLift f Z d t)).trans (Category.assoc _ _ _)

lemma extends_action (X Y : ResolutionObject C) (f : X.base ⟶ Y.base) (Z : C)
    {K L : SSet.{v}} (i : K ⟶ L) [Mono i] (b : K ⟶ ResolutionLiftSpace.obj X Y f)
    (t : L ⟶ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom Y.resolution.obj).obj Z) :
    ∃ e : L ⟶ ResolutionLiftSpace.obj X Y f, i ≫ e = b ∧
      i ≫ parameterized hcof hfib X Y f Z e t =
        parameterized hcof hfib X Y f Z b (i ≫ t) := by
  obtain ⟨e, he, ha⟩ := ResolutionLiftAction.extends_action hcof X Y f Z i b t
  exact ⟨e, he, (Category.assoc _ _ _).symm.trans
    (congrArg (fun k => k ≫ (SimplicialModel.KanReplacement.unit hcof hfib).app
      (ResolutionLiftAction.target X Z)) ha)⟩

lemma comparison_piZero_bijective (X : ResolutionObject C) (Z : C) [IsFibrant Z] :
    Function.Bijective (SSet.mapπ₀ (comparison hcof hfib X Z)) := by
  have : SSet.KanComplex ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom X.resolution.obj).obj Z) :=
    cosimplicialHom_kanComplex _ X.resolution.cofibrant X.resolution.homotopicallyConstant Z
  have : IsFibrant ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom X.resolution.obj).obj Z) :=
    SimplicialModel.KanReplacement.isFibrant_of_kanComplex hfib _
  have : IsFibrant (target hcof hfib X Z) := SimplicialModel.KanReplacement.isFibrant _ _ _
  have : WeakEquivalence (comparison hcof hfib X Z) := ⟨comparison_weakEquivalence _ _ X Z⟩
  exact SimplicialModel.piZero_bijective_of_weakEquivalence_of_fibrant hcof _

/-- Components of the actual Kan target are the ordinary localized hom set. -/
def piZeroLocalizationEquiv {H : Type uH} [Category.{vH} H] (Q : C ⥤ H)
    [Q.IsLocalization (weakEquivalences C)] (X : ResolutionObject C) (Z : C) [IsFibrant Z] :
    SSet.π₀ (target hcof hfib X Z) ≃ (Q.obj X.base ⟶ Q.obj Z) :=
  (Equiv.ofBijective (SSet.mapπ₀ (comparison hcof hfib X Z))
    (comparison_piZero_bijective hcof hfib X Z)).symm.trans
      (resolutionPiZeroLocalizationEquiv Q X.resolution Z)

end SerrePositivity.HomotopyFunctionComplex.KanLiftAction
