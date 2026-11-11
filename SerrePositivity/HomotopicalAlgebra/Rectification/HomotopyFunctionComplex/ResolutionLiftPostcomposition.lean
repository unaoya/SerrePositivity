module

public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.CoherentLiftTuples

/-!
# 中断した任意モデル源への一般化：ResolutionLiftPostcomposition

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：Actual postcomposition of higher resolution-lift families。

## 方針（定義・証明）
frameによる導来写像空間と整合図式の厳密化に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0308][inventory]を参照する。

[inventory]: ../../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0308
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Actual postcomposition of higher resolution-lift families

A strict map of target resolutions postcomposes an entire lift family,
including its prescribed boundary. Its action is the same as first
precomposing the original Hom along that strict map. This connects lift
spaces over different base maps, without a source factorization functor.
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra

namespace SerrePositivity.HomotopyFunctionComplex.ResolutionLiftPostcomposition
variable {C : Type u} [Category.{v} C] [ModelCategory C]
local instance : ModelCategory (SimplexCategory ⥤ C) := Reedy.simplexModelCategory C

def map (X Y W : ResolutionObject C) (f : X.base ⟶ Y.base) (g : Y ⟶ W) :
    ResolutionLiftSpace.obj X Y f ⟶ ResolutionLiftSpace.obj X W (f ≫ g.base) :=
  pullback.lift
    (LiftSpace.inclusion (ResolutionLiftSpace.frame X).obj
      (ResolutionLiftSpace.frame X).augmentation
      Y.resolution.augmentation (ResolutionLiftSpace.baseMap X Y f) ≫
        (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom (ResolutionLiftSpace.frame X).obj).map g.diagram)
    (ResolutionLiftSpace.projection X Y f) (by
      rw [Category.assoc, ← Functor.map_comp, g.over, Functor.map_comp, ← Category.assoc,
        LiftSpace.over, Category.assoc, LiftSpace.point_postcomp]
      congr 2
      simp only [ResolutionLiftSpace.baseMap, Functor.map_comp, Category.assoc])

@[reassoc (attr := simp)]
lemma map_inclusion (X Y W : ResolutionObject C) (f : X.base ⟶ Y.base) (g : Y ⟶ W) :
    map X Y W f g ≫ LiftSpace.inclusion (ResolutionLiftSpace.frame X).obj
        (ResolutionLiftSpace.frame X).augmentation W.resolution.augmentation
        (ResolutionLiftSpace.baseMap X W (f ≫ g.base)) =
      LiftSpace.inclusion (ResolutionLiftSpace.frame X).obj
        (ResolutionLiftSpace.frame X).augmentation Y.resolution.augmentation
        (ResolutionLiftSpace.baseMap X Y f) ≫
          (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom (ResolutionLiftSpace.frame X).obj).map g.diagram :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma map_projection (X Y W : ResolutionObject C) (f : X.base ⟶ Y.base) (g : Y ⟶ W) :
    map X Y W f g ≫ ResolutionLiftSpace.projection X W (f ≫ g.base) =
      ResolutionLiftSpace.projection X Y f := pullback.lift_snd _ _ _

lemma ofLift {X Y W : ResolutionObject C} (k : X ⟶ Y) (g : Y ⟶ W) :
    ResolutionLiftSpace.ofLift k ≫ map X Y W k.base g = ResolutionLiftSpace.ofLift (k ≫ g) := by
  apply pullback.hom_ext
  · simp only [Category.assoc, map_inclusion, ResolutionLiftSpace.ofLift,
      LiftSpace.ofLift_inclusion_assoc, LiftSpace.point_postcomp]
    exact (LiftSpace.ofLift_inclusion (ResolutionLiftSpace.frame X).obj
      (ResolutionLiftSpace.frame X).augmentation W.resolution.augmentation
      (ResolutionLiftSpace.baseMap X W (k ≫ g).base) (k ≫ g).diagram (k ≫ g).over).symm
  · simp only [Category.assoc, map_projection, ResolutionLiftSpace.ofLift,
      LiftSpace.ofLift_projection]
    exact (LiftSpace.ofLift_projection (ResolutionLiftSpace.frame X).obj
      (ResolutionLiftSpace.frame X).augmentation W.resolution.augmentation
      (ResolutionLiftSpace.baseMap X W (k ≫ g).base) (k ≫ g).diagram (k ≫ g).over).symm

/-- Postcompose any higher family, including the entire already prescribed boundary. -/
lemma boundary (X Y W : ResolutionObject C) (f : X.base ⟶ Y.base) (g : Y ⟶ W)
    {K L : SSet.{v}} (i : K ⟶ L) (b : K ⟶ ResolutionLiftSpace.obj X Y f)
    (e : L ⟶ ResolutionLiftSpace.obj X Y f) (he : i ≫ e = b) :
    i ≫ (e ≫ map X Y W f g) = b ≫ map X Y W f g := by
  rw [← Category.assoc, he]

lemma raw_action (X Y W : ResolutionObject C) (f : X.base ⟶ Y.base) (g : Y ⟶ W)
    (Z : C) {T : SSet.{v}} (s : T ⟶ ResolutionLiftSpace.obj X Y f)
    (t : T ⟶ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom W.resolution.obj).obj Z) :
    ResolutionLiftAction.parameterized X W (f ≫ g.base) Z (s ≫ map X Y W f g) t =
      ResolutionLiftAction.parameterized X Y f Z s (t ≫ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHomMap g.diagram).app Z) := by
  change DiagonalHom.pairing _ _ _ ((_ ≫ map X Y W f g) ≫ _) t =
    DiagonalHom.pairing _ _ _ (_ ≫ _) _
  rw [Category.assoc, map_inclusion, ← Category.assoc]
  exact DiagonalHom.pairing_middle_naturality _ _ _ g.diagram _ _

variable [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)

lemma kan_action (X Y W : ResolutionObject C) (f : X.base ⟶ Y.base) (g : Y ⟶ W)
    (Z : C) {T : SSet.{v}} (s : T ⟶ ResolutionLiftSpace.obj X Y f)
    (t : T ⟶ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom W.resolution.obj).obj Z) :
    KanLiftAction.parameterized hcof hfib X W (f ≫ g.base) Z (s ≫ map X Y W f g) t =
      KanLiftAction.parameterized hcof hfib X Y f Z s
        (t ≫ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHomMap g.diagram).app Z) := by
  exact congrArg (fun k => k ≫ (SimplicialModel.KanReplacement.unit hcof hfib).app
    (ResolutionLiftAction.target X Z)) (raw_action X Y W f g Z s t)

end SerrePositivity.HomotopyFunctionComplex.ResolutionLiftPostcomposition
