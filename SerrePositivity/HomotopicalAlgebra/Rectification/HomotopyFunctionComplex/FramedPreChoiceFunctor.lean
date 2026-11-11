module

public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.FramedResolutionCategory
public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.CoherentLiftPreComposition
public import SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.RelativeChoiceFunctor
public import Mathlib.CategoryTheory.Comma.Over.Basic

/-!
# 中断した任意モデル源への一般化：FramedPreChoiceFunctor

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：Strict source precomposition over actual framed contexts。

## 方針（定義・証明）
自明fibrationのファイバーと相対延長による選択の比較に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0089][inventory]を参照する。

[inventory]: ../../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0089
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Strict source precomposition over actual framed contexts

The over category records the actual frame maps and commuting triangles.
Its opposite acts on lift spaces and on the original precomparison spaces.
No independently chosen composite frame lift is used.
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SerrePositivity.SimplicialModel
open SerrePositivity.HomotopyFunctionComplex.CoherentLiftRelative

namespace SerrePositivity.HomotopyFunctionComplex.FramedPreChoiceFunctor
variable {C : Type u} [Category.{v} C] [ModelCategory C]
local instance : ModelCategory (SimplexCategory ⥤ C) := Reedy.simplexModelCategory C

abbrev raw (W : ResolutionObject C) : (FramedResolution C)ᵒᵖ ⥤ SSet.{v} :=
  FramedResolution.outerDiagrams.op ⋙ cosimplicialHomSource W.resolution.obj

variable {Y : FramedResolution C} (W : ResolutionObject C) (g : Y.inner.base ⟶ W.base)

abbrev fiber (a : Over Y) : SSet.{v} :=
  ResolutionLiftSpace.obj a.left.inner W (a.hom.map.base ≫ g)

lemma base_square {a b : Over Y} (k : a ⟶ b) :
    k.left.map.diagram ≫ ResolutionLiftSpace.baseMap b.left.inner W (b.hom.map.base ≫ g) =
      ResolutionLiftSpace.baseMap a.left.inner W (a.hom.map.base ≫ g) := by
  have hb : k.left.map.base ≫ b.hom.map.base = a.hom.map.base :=
    congrArg (fun q => q.map.base) (Over.w k)
  change k.left.map.diagram ≫ (b.left.inner.resolution.augmentation ≫
    (Functor.const SimplexCategory).map (b.hom.map.base ≫ g)) =
      a.left.inner.resolution.augmentation ≫
        (Functor.const SimplexCategory).map (a.hom.map.base ≫ g)
  rw [← Category.assoc, k.left.map.over, Category.assoc, ← CategoryTheory.Functor.map_comp]
  exact congrArg (fun q => a.left.inner.resolution.augmentation ≫
    (Functor.const SimplexCategory).map q)
      ((Category.assoc _ _ _).symm.trans (congrArg (fun q => q ≫ g) hb))

/-- A direct map of the actual fibers, with the context triangle retained in its base square. -/
def fiberMap {a b : Over Y} (k : a ⟶ b) : fiber W g b ⟶ fiber W g a :=
  LiftSpacePrecomposition.map (ResolutionLiftSpace.frame a.left.inner).obj
    (ResolutionLiftSpace.frame b.left.inner).obj
    (ResolutionLiftSpace.frame a.left.inner).augmentation
    (ResolutionLiftSpace.frame b.left.inner).augmentation
    k.left.map.diagram k.left.frame k.left.over
    W.resolution.augmentation (ResolutionLiftSpace.baseMap a.left.inner W (a.hom.map.base ≫ g))
    (ResolutionLiftSpace.baseMap b.left.inner W (b.hom.map.base ≫ g)) (base_square W g k)

lemma base_eq {a b : Over Y} (k : a ⟶ b) :
    k.left.map.base ≫ (b.hom.map.base ≫ g) = a.hom.map.base ≫ g :=
  (Category.assoc _ _ _).symm.trans
    (congrArg (fun q => q ≫ g) (congrArg (fun q => q.map.base) (Over.w k)))

@[reassoc]
lemma fiberMap_inclusion {a b : Over Y} (k : a ⟶ b) :
    fiberMap W g k ≫ ResolutionLiftSpace.inclusion a.left.inner W (a.hom.map.base ≫ g) =
      ResolutionLiftSpace.inclusion b.left.inner W (b.hom.map.base ≫ g) ≫
        (raw W).map k.left.op := pullback.lift_fst _ _ _

@[reassoc]
lemma fiberMap_projection {a b : Over Y} (k : a ⟶ b) :
    fiberMap W g k ≫ ResolutionLiftSpace.projection a.left.inner W (a.hom.map.base ≫ g) =
      ResolutionLiftSpace.projection b.left.inner W (b.hom.map.base ≫ g) := pullback.lift_snd _ _ _

/-- The contextual fiber map is the existing actual precomposition followed by its base cast. -/
lemma fiberMap_existing {a b : Over Y} (k : a ⟶ b) : fiberMap W g k =
    ResolutionLiftPrecomposition.map a.left.inner b.left.inner W k.left.map
        (b.hom.map.base ≫ g) (FramedResolution.frameMap k.left) ≫
      ResolutionLiftSpace.baseChange (base_eq W g k) := by
  apply ResolutionLiftSpace.hom_ext
  · have hr := (Category.assoc
        (ResolutionLiftPrecomposition.map a.left.inner b.left.inner W k.left.map
          (b.hom.map.base ≫ g) (FramedResolution.frameMap k.left))
        (ResolutionLiftSpace.baseChange (base_eq W g k))
        (ResolutionLiftSpace.inclusion a.left.inner W (a.hom.map.base ≫ g))).trans
      ((congrArg (fun q => ResolutionLiftPrecomposition.map a.left.inner b.left.inner W k.left.map
        (b.hom.map.base ≫ g) (FramedResolution.frameMap k.left) ≫ q)
        (ResolutionLiftSpace.baseChange_inclusion (base_eq W g k))).trans
          (ResolutionLiftSpace.pre_inclusion _ _ _ _ _ _))
    exact (fiberMap_inclusion W g k).trans hr.symm
  · have hr := (Category.assoc
        (ResolutionLiftPrecomposition.map a.left.inner b.left.inner W k.left.map
          (b.hom.map.base ≫ g) (FramedResolution.frameMap k.left))
        (ResolutionLiftSpace.baseChange (base_eq W g k))
        (ResolutionLiftSpace.projection a.left.inner W (a.hom.map.base ≫ g))).trans
      ((congrArg (fun q => ResolutionLiftPrecomposition.map a.left.inner b.left.inner W k.left.map
        (b.hom.map.base ≫ g) (FramedResolution.frameMap k.left) ≫ q)
        (ResolutionLiftSpace.baseChange_projection (base_eq W g k))).trans
          (ResolutionLiftSpace.pre_projection _ _ _ _ _ _))
    exact (fiberMap_projection W g k).trans hr.symm

lemma fiberMap_identity (a : Over Y) : fiberMap W g (𝟙 a) = 𝟙 (fiber W g a) := by
  apply ResolutionLiftSpace.hom_ext
  · have hi := fiberMap_inclusion W g (𝟙 a)
    have hr := congrArg (fun q => ResolutionLiftSpace.inclusion a.left.inner W
      (a.hom.map.base ≫ g) ≫ q) ((raw W).map_id (Opposite.op a.left))
    exact hi.trans (hr.trans ((Category.comp_id _).trans (Category.id_comp _).symm))
  · exact (fiberMap_projection W g (𝟙 a)).trans (Category.id_comp _).symm

lemma fiberMap_compose {a b c : Over Y} (k : a ⟶ b) (l : b ⟶ c) :
    fiberMap W g (k ≫ l) = fiberMap W g l ≫ fiberMap W g k := by
  apply ResolutionLiftSpace.hom_ext
  · have hr := (Category.assoc (fiberMap W g l) (fiberMap W g k)
        (ResolutionLiftSpace.inclusion a.left.inner W (a.hom.map.base ≫ g))).trans
      ((congrArg (fun q => fiberMap W g l ≫ q) (fiberMap_inclusion W g k)).trans
        ((Category.assoc _ _ _).symm.trans
          ((congrArg (fun q => q ≫ (raw W).map k.left.op) (fiberMap_inclusion W g l)).trans
            (Category.assoc _ _ _))))
    have hm := congrArg (fun q => ResolutionLiftSpace.inclusion c.left.inner W
      (c.hom.map.base ≫ g) ≫ q) ((raw W).map_comp l.left.op k.left.op)
    exact (fiberMap_inclusion W g (k ≫ l)).trans (hm.trans hr.symm)
  · exact (fiberMap_projection W g (k ≫ l)).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun q => fiberMap W g l ≫ q) (fiberMap_projection W g k)).trans
          (fiberMap_projection W g l))).symm

/-- A strict small-valued diagram, with no new composite frame choices. -/
def fibers : (Over Y)ᵒᵖ ⥤ SSet.{v} where
  obj a := fiber W g a.unop
  map k := fiberMap W g k.unop
  map_id a := fiberMap_identity W g a.unop
  map_comp k l := fiberMap_compose W g l.unop k.unop

abbrev baseLiftMap (a : Over Y) : ResolutionLiftSpace.obj Y.inner W g ⟶ fiber W g a :=
  ResolutionLiftPrecomposition.map a.left.inner Y.inner W a.hom.map g
    (FramedResolution.frameMap a.hom)

@[reassoc]
lemma baseLiftMap_inclusion (a : Over Y) : baseLiftMap W g a ≫
    ResolutionLiftSpace.inclusion a.left.inner W (a.hom.map.base ≫ g) =
      ResolutionLiftSpace.inclusion Y.inner W g ≫ (raw W).map a.hom.op :=
  ResolutionLiftSpace.pre_inclusion _ _ _ _ _ _

lemma baseLiftMap_naturality {a b : Over Y} (k : a ⟶ b) :
    baseLiftMap W g b ≫ fiberMap W g k = baseLiftMap W g a := by
  apply ResolutionLiftSpace.hom_ext
  · rw [Category.assoc, fiberMap_inclusion, ← Category.assoc, baseLiftMap_inclusion,
      Category.assoc, baseLiftMap_inclusion]
    have hw : b.hom.op ≫ k.left.op = a.hom.op := congrArg Quiver.Hom.op (Over.w k)
    have hr := ((raw W).map_comp b.hom.op k.left.op).symm.trans (congrArg (raw W).map hw)
    exact congrArg (fun q => ResolutionLiftSpace.inclusion Y.inner W g ≫ q) hr
  · rw [Category.assoc, fiberMap_projection]
    exact (ResolutionLiftSpace.pre_projection _ _ _ _ _ _).trans
      (ResolutionLiftSpace.pre_projection _ _ _ _ _ _).symm

variable [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)

/-- The existing preLeft families are one actual natural transformation. -/
def leftFamily : (Functor.const (Over Y)ᵒᵖ).obj (CoherentLiftTuples.obj Y.inner W g) ⟶
    fibers W g where
  app a := preLeft hcof a.unop.left.inner Y.inner W a.unop.hom.map g
    (FramedResolution.frameMap a.unop.hom)
  naturality {a b} k := by
    change (𝟙 _) ≫ _ = _
    rw [Category.id_comp]
    exact ((Category.assoc _ _ _).trans
      (congrArg (fun q => CoherentLiftTuples.interpolation hcof Y.inner W g ≫ q)
        (baseLiftMap_naturality W g k.unop))).symm

/-- Fixed strict-lift vertex data are natural throughout the framed over category. -/
def boundary : (Functor.const (Over Y)ᵒᵖ).obj (vertices Y.inner W g) ⟶ fibers W g where
  app a := preBoundary a.unop.left.inner Y.inner W a.unop.hom.map g
  naturality {a b} k := by
    have ha := preLeft_vertices hcof a.unop.left.inner Y.inner W a.unop.hom.map g
      (FramedResolution.frameMap a.unop.hom)
    have hb := preLeft_vertices hcof b.unop.left.inner Y.inner W b.unop.hom.map g
      (FramedResolution.frameMap b.unop.hom)
    change (𝟙 _) ≫ _ = _
    rw [Category.id_comp]
    have hn : preLeft hcof b.unop.left.inner Y.inner W b.unop.hom.map g
        (FramedResolution.frameMap b.unop.hom) =
        preLeft hcof a.unop.left.inner Y.inner W a.unop.hom.map g
          (FramedResolution.frameMap a.unop.hom) ≫ fiberMap W g k.unop :=
      (Category.id_comp _).symm.trans ((leftFamily W g hcof).naturality k)
    exact hb.symm.trans
      ((congrArg (fun q => vertexInclusion Y.inner W g ≫ q) hn).trans
        ((Category.assoc _ _ _).symm.trans
          (congrArg (fun q => q ≫ fiberMap W g k.unop) ha)))

/-- All source precomparison spaces, with values in the original Hom universe. -/
abbrev functor : (Over Y)ᵒᵖ ⥤ SSet.{v} :=
  RelativeChoiceFunctor.functor (fibers W g) (vertexInclusion Y.inner W g) (boundary W g hcof)

abbrev point : (Functor.const (Over Y)ᵒᵖ).obj
    (SSet.stdSimplex.{v}.obj (SimplexCategory.mk 0)) ⟶ functor W g hcof :=
  RelativeChoiceFunctor.point (fibers W g) (vertexInclusion Y.inner W g) (boundary W g hcof)
    (leftFamily W g hcof) (fun a => preLeft_vertices hcof a.unop.left.inner Y.inner W
      a.unop.hom.map g (FramedResolution.frameMap a.unop.hom))

abbrev projection : functor W g hcof ⟶ (Functor.const (Over Y)ᵒᵖ).obj
    (SSet.stdSimplex.{v}.obj (SimplexCategory.mk 0)) :=
  RelativeChoiceFunctor.projection (fibers W g) (vertexInclusion Y.inner W g) (boundary W g hcof)

lemma point_projection : point W g hcof ≫ projection W g hcof = 𝟙 _ :=
  RelativeChoiceFunctor.point_projection _ _ _ _ _

lemma functor_obj (a : (Over Y)ᵒᵖ) : (functor W g hcof).obj a =
    preChoiceSpace a.unop.left.inner Y.inner W a.unop.hom.map g := rfl

lemma point_component (a : (Over Y)ᵒᵖ) : (point W g hcof).app a =
    preLeftPoint hcof a.unop.left.inner Y.inner W a.unop.hom.map g
      (FramedResolution.frameMap a.unop.hom) := rfl

lemma projection_trivialFibration
    (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp) (a : (Over Y)ᵒᵖ) :
    trivialFibrations SSet.{v} ((projection W g hcof).app a) :=
  _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.projection_trivialFibration hcof hfib (vertexInclusion Y.inner W g)
    (preBoundary a.unop.left.inner Y.inner W a.unop.hom.map g)
    (ResolutionLiftSpace.projection a.unop.left.inner W (a.unop.hom.map.base ≫ g))
    (ResolutionLiftSpace.projection_trivialFibration hcof a.unop.left.inner W
      (a.unop.hom.map.base ≫ g))

lemma point_weakEquivalence
    (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp) (a : (Over Y)ᵒᵖ) :
    weakEquivalences SSet.{v} ((point W g hcof).app a) := by
  have hp := projection_trivialFibration W g hcof hfib a
  have he : (point W g hcof).app a ≫ (projection W g hcof).app a = 𝟙 _ :=
    congr_app (point_projection W g hcof) a
  exact (weakEquivalences SSet.{v}).of_postcomp _ _ hp.2
    (he.symm ▸ (weakEquivalences SSet.{v}).id_mem _)

end SerrePositivity.HomotopyFunctionComplex.FramedPreChoiceFunctor
