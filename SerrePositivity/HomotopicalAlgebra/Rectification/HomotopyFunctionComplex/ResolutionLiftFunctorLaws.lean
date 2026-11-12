module

public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.ResolutionLiftPrecomposition

/-!
# 中断した任意モデル源への一般化：ResolutionLiftFunctorLaws

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：Exact unit, composition, and interchange laws for actual lift transports。

## 方針（定義・証明）
frameによる導来写像空間と整合図式の厳密化に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0306][inventory]を参照する。

[inventory]: ../../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0306
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Exact unit, composition, and interchange laws for actual lift transports

The base map of a lift space is indexed. Explicit equality transports retain
its inclusion and projection, so associativity of base maps is not treated
as definitional equality. Actual frame composites are used throughout;
independently chosen frame lifts are not asserted to form a functor.
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra

namespace SerrePositivity.HomotopyFunctionComplex
variable {C : Type u} [Category.{v} C] [ModelCategory C]
local instance : ModelCategory (SimplexCategory ⥤ C) := Reedy.simplexModelCategory C

namespace ResolutionLiftSpace

abbrev inclusion (X Y : ResolutionObject C) (f : X.base ⟶ Y.base) :=
  LiftSpace.inclusion (frame X).obj (frame X).augmentation Y.resolution.augmentation (baseMap X Y f)

def baseChange {X Y : ResolutionObject C} {f g : X.base ⟶ Y.base} (h : f = g) :
    obj X Y f ⟶ obj X Y g := eqToHom (congrArg (obj X Y) h)

@[simp]
lemma baseChange_refl {X Y : ResolutionObject C} (f : X.base ⟶ Y.base) :
    baseChange (rfl : f = f) = 𝟙 (obj X Y f) := rfl

@[simp]
lemma baseChange_trans {X Y : ResolutionObject C} {f g h : X.base ⟶ Y.base}
    (hfg : f = g) (hgh : g = h) :
    baseChange hfg ≫ baseChange hgh = baseChange (hfg.trans hgh) := by
  cases hfg
  cases hgh
  rfl

@[reassoc (attr := simp)]
lemma baseChange_symm {X Y : ResolutionObject C} {f g : X.base ⟶ Y.base} (h : f = g) :
    baseChange h ≫ baseChange h.symm = 𝟙 (obj X Y f) := by cases h; rfl

@[reassoc (attr := simp)]
lemma baseChange_inclusion {X Y : ResolutionObject C} {f g : X.base ⟶ Y.base} (h : f = g) :
    baseChange h ≫ inclusion X Y g = inclusion X Y f := by cases h; exact Category.id_comp _

@[reassoc (attr := simp)]
lemma baseChange_projection {X Y : ResolutionObject C} {f g : X.base ⟶ Y.base} (h : f = g) :
    baseChange h ≫ projection X Y g = projection X Y f := by cases h; exact Category.id_comp _

lemma hom_ext {X Y : ResolutionObject C} {f : X.base ⟶ Y.base} {T : SSet.{v}}
    {s t : T ⟶ obj X Y f} (hi : s ≫ inclusion X Y f = t ≫ inclusion X Y f)
    (hp : s ≫ projection X Y f = t ≫ projection X Y f) : s = t := pullback.hom_ext hi hp

@[reassoc]
lemma post_inclusion (X Y W : ResolutionObject C) (f : X.base ⟶ Y.base) (g : Y ⟶ W) :
    ResolutionLiftPostcomposition.map X Y W f g ≫ inclusion X W (f ≫ g.base) =
      inclusion X Y f ≫ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom (frame X).obj).map g.diagram :=
  ResolutionLiftPostcomposition.map_inclusion X Y W f g

@[reassoc]
lemma pre_inclusion (X Y W : ResolutionObject C) (f : X ⟶ Y) (g : Y.base ⟶ W.base)
    (φ : ResolutionLiftPrecomposition.FrameMap f) :
    ResolutionLiftPrecomposition.map X Y W f g φ ≫ inclusion X W (f.base ≫ g) =
      inclusion Y W g ≫ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHomMap φ.val).app W.resolution.obj :=
  LiftSpacePrecomposition.map_inclusion _ _ _ _ _ _ _ _ _ _ _

@[reassoc]
lemma pre_projection (X Y W : ResolutionObject C) (f : X ⟶ Y) (g : Y.base ⟶ W.base)
    (φ : ResolutionLiftPrecomposition.FrameMap f) :
    ResolutionLiftPrecomposition.map X Y W f g φ ≫ projection X W (f.base ≫ g) =
      projection Y W g := LiftSpacePrecomposition.map_projection _ _ _ _ _ _ _ _ _ _ _

end ResolutionLiftSpace

namespace ResolutionLiftFunctorLaws
open ResolutionLiftSpace

lemma post_identity (X Y : ResolutionObject C) (f : X.base ⟶ Y.base) :
    ResolutionLiftPostcomposition.map X Y Y f (𝟙 Y) ≫ baseChange (Category.comp_id f) = 𝟙 _ := by
  apply ResolutionLiftSpace.hom_ext
  · simp only [Category.assoc, baseChange_inclusion, post_inclusion, Category.id_comp]
    change inclusion X Y f ≫ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom (frame X).obj).map (𝟙 Y.resolution.obj) = _
    rw [CategoryTheory.Functor.map_id, Category.comp_id]
  · simp only [Category.assoc, baseChange_projection, ResolutionLiftPostcomposition.map_projection,
      Category.id_comp]

lemma post_compose (X Y W V : ResolutionObject C) (f : X.base ⟶ Y.base)
    (g : Y ⟶ W) (h : W ⟶ V) :
    ResolutionLiftPostcomposition.map X Y W f g ≫
        ResolutionLiftPostcomposition.map X W V (f ≫ g.base) h ≫
          baseChange (Category.assoc f g.base h.base) =
      ResolutionLiftPostcomposition.map X Y V f (g ≫ h) := by
  apply ResolutionLiftSpace.hom_ext
  · simp only [Category.assoc, baseChange_inclusion, post_inclusion, post_inclusion_assoc]
    exact (congrArg (fun k => inclusion X Y f ≫ k)
      ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom (frame X).obj).map_comp g.diagram h.diagram).symm).trans
        (post_inclusion X Y V f (g ≫ h)).symm
  · simp only [Category.assoc, baseChange_projection, ResolutionLiftPostcomposition.map_projection]
    exact (ResolutionLiftPostcomposition.map_projection X Y V f (g ≫ h)).symm

lemma pre_identity (X W : ResolutionObject C) (g : X.base ⟶ W.base) :
    ResolutionLiftPrecomposition.map X X W (𝟙 X) g (ResolutionLiftPrecomposition.identity X) ≫
        baseChange (Category.id_comp g) = 𝟙 _ := by
  apply ResolutionLiftSpace.hom_ext
  · simp only [Category.assoc, baseChange_inclusion, pre_inclusion, Category.id_comp]
    have hi : (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHomMap (ResolutionLiftPrecomposition.identity X).val).app
        W.resolution.obj = 𝟙 _ := by
      ext n x
      exact Category.id_comp x
    rw [hi, Category.comp_id]
  · simp only [Category.assoc, baseChange_projection, pre_projection, Category.id_comp]

lemma pre_compose (X Y W V : ResolutionObject C) (f : X ⟶ Y) (g : Y ⟶ W)
    (h : W.base ⟶ V.base) (φ : ResolutionLiftPrecomposition.FrameMap f)
    (ψ : ResolutionLiftPrecomposition.FrameMap g) :
    ResolutionLiftPrecomposition.map Y W V g h ψ ≫
        ResolutionLiftPrecomposition.map X Y V f (g.base ≫ h) φ =
      ResolutionLiftPrecomposition.map X W V (f ≫ g) h
          (ResolutionLiftPrecomposition.compose φ ψ) ≫
            baseChange (Category.assoc f.base g.base h) := by
  apply ResolutionLiftSpace.hom_ext
  · simp only [Category.assoc, baseChange_inclusion, pre_inclusion, pre_inclusion_assoc]
    have hc : (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHomMap (ResolutionLiftPrecomposition.compose φ ψ).val).app
        V.resolution.obj =
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHomMap ψ.val).app V.resolution.obj ≫
        (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHomMap φ.val).app V.resolution.obj := by
      ext n x
      exact Category.assoc _ _ _
    rw [hc]
  · simp only [Category.assoc, baseChange_projection, pre_projection]

/-- Precomposition and postcomposition commute as actual maps of lift spaces. -/
lemma interchange (X Y W V : ResolutionObject C) (f : X ⟶ Y) (g : Y.base ⟶ W.base)
    (h : W ⟶ V) (φ : ResolutionLiftPrecomposition.FrameMap f) :
    ResolutionLiftPrecomposition.map X Y W f g φ ≫
        ResolutionLiftPostcomposition.map X W V (f.base ≫ g) h ≫
          baseChange (Category.assoc f.base g h.base) =
      ResolutionLiftPostcomposition.map Y W V g h ≫
        ResolutionLiftPrecomposition.map X Y V f (g ≫ h.base) φ := by
  apply ResolutionLiftSpace.hom_ext
  · simp only [Category.assoc, baseChange_inclusion, pre_inclusion, post_inclusion,
      pre_inclusion_assoc, post_inclusion_assoc]
    exact congrArg (fun k => inclusion Y W g ≫ k)
      ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHomMap φ.val).naturality h.diagram).symm
  · simp only [Category.assoc, baseChange_projection, pre_projection,
      ResolutionLiftPostcomposition.map_projection]

end ResolutionLiftFunctorLaws
end SerrePositivity.HomotopyFunctionComplex
