module

public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.FramedPreChoiceFunctor
public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.Pullbacks.FiberFunctor

/-!
# 中断した任意モデル源への一般化：MixedChoiceFunctor

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：One strict diagram for simultaneous source and target contexts。

## 方針（定義・証明）
自明fibrationのファイバーと相対延長による選択の比較に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0117][inventory]を参照する。

[inventory]: ../../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0117
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# One strict diagram for simultaneous source and target contexts

The source over category records actual frame maps. The target under
category records actual resolution maps. Ordinary functorial pullback
fibers retain their mixed action and strict interchange.
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SerrePositivity.SimplicialModel
open SerrePositivity.HomotopyFunctionComplex.CoherentLiftRelative

namespace SerrePositivity.HomotopyFunctionComplex.MixedChoiceFunctor
variable {C : Type u} [Category.{v} C] [ModelCategory C]
local instance : ModelCategory (SimplexCategory ⥤ C) := Reedy.simplexModelCategory C

abbrev rawBifunctor : (FramedResolution C)ᵒᵖ ⥤ (SimplexCategory ⥤ C) ⥤ SSet.{v} :=
  FramedResolution.outerDiagrams.op ⋙ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHomBifunctor

abbrev baseDiagrams : ResolutionObject C ⥤ SimplexCategory ⥤ C :=
  ResolutionObject.projection ⋙ Functor.const SimplexCategory

def targetAugmentation : ResolutionObject.diagrams (C := C) ⟶ baseDiagrams where
  app W := W.resolution.augmentation
  naturality {_ _} f := f.over

abbrev rawPairs : (FramedResolution C)ᵒᵖ × ResolutionObject C ⥤ SSet.{v} :=
  Functor.uncurry.obj (rawBifunctor ⋙
    (Functor.whiskeringLeft (ResolutionObject C) (SimplexCategory ⥤ C) SSet.{v}).obj
      ResolutionObject.diagrams)

abbrev basePairs : (FramedResolution C)ᵒᵖ × ResolutionObject C ⥤ SSet.{v} :=
  Functor.uncurry.obj (rawBifunctor ⋙
    (Functor.whiskeringLeft (ResolutionObject C) (SimplexCategory ⥤ C) SSet.{v}).obj baseDiagrams)

def pairProjection : rawPairs (C := C) ⟶ basePairs :=
  Functor.uncurry.map (Functor.whiskerLeft rawBifunctor
    ((Functor.whiskeringLeft (ResolutionObject C) (SimplexCategory ⥤ C) SSet.{v}).map
      targetAugmentation))

variable (Y : FramedResolution C) (W : ResolutionObject C)
abbrev Context := (Over Y)ᵒᵖ × Under W
abbrev contexts : Context Y W ⥤ (FramedResolution C)ᵒᵖ × ResolutionObject C :=
  (Over.forget Y).op.prod (Under.forget W)

abbrev raw : Context Y W ⥤ SSet.{v} := contexts Y W ⋙ rawPairs
abbrev base : Context Y W ⥤ SSet.{v} := contexts Y W ⋙ basePairs
abbrev rawProjection : raw Y W ⟶ base Y W := Functor.whiskerLeft (contexts Y W) pairProjection

abbrev rootMap (t : Context Y W) : (Opposite.op Y, W) ⟶ (contexts Y W).obj t :=
  (t.1.unop.hom.op, t.2.hom)

lemma rootMap_naturality {s t : Context Y W} (k : s ⟶ t) :
    rootMap Y W s ≫ (contexts Y W).map k = rootMap Y W t := by
  apply Prod.ext
  · exact congrArg Quiver.Hom.op (Over.w k.1.unop)
  · exact Under.w k.2

/-- The context arrows give a strictly natural cone for any pair diagram. -/
def rootCone (F : (FramedResolution C)ᵒᵖ × ResolutionObject C ⥤ SSet.{v}) :
    (Functor.const (Context Y W)).obj (F.obj (Opposite.op Y, W)) ⟶ contexts Y W ⋙ F where
  app t := F.map (rootMap Y W t)
  naturality {s t} k := by
    change (𝟙 _) ≫ F.map (rootMap Y W t) =
      F.map (rootMap Y W s) ≫ F.map ((contexts Y W).map k)
    rw [Category.id_comp, ← F.map_comp, rootMap_naturality]

variable (g : Y.inner.base ⟶ W.base)

abbrev rootPoint : SSet.stdSimplex.{v}.obj (SimplexCategory.mk 0) ⟶
    (basePairs (C := C)).obj (Opposite.op Y, W) :=
  LiftSpace.point (ResolutionLiftSpace.frame Y.inner).obj
    (ResolutionLiftSpace.frame Y.inner).augmentation
    (ResolutionLiftSpace.baseMap Y.inner W g)

def basepoint : (Functor.const (Context Y W)).obj
    (SSet.stdSimplex.{v}.obj (SimplexCategory.mk 0)) ⟶ base Y W :=
  (Functor.const (Context Y W)).map (rootPoint Y W g) ≫ rootCone Y W basePairs

abbrev total (t : Context Y W) : t.1.unop.left.inner.base ⟶ t.2.right.base :=
  t.1.unop.hom.map.base ≫ g ≫ t.2.hom.base

lemma basepoint_eq (t : Context Y W) : (basepoint Y W g).app t =
    LiftSpace.point (ResolutionLiftSpace.frame t.1.unop.left.inner).obj
      (ResolutionLiftSpace.frame t.1.unop.left.inner).augmentation
      (ResolutionLiftSpace.baseMap t.1.unop.left.inner t.2.right (total Y W g t)) := by
  let a := t.1.unop.hom
  have hb : a.map.diagram ≫ ResolutionLiftSpace.baseMap Y.inner W g =
      ResolutionLiftSpace.baseMap t.1.unop.left.inner W (a.map.base ≫ g) := by
    dsimp [ResolutionLiftSpace.baseMap]
    rw [← Category.assoc, a.map.over, Category.assoc, Functor.map_comp]
  have hp := LiftSpacePrecomposition.point
    (ResolutionLiftSpace.frame t.1.unop.left.inner).obj (ResolutionLiftSpace.frame Y.inner).obj
    (ResolutionLiftSpace.frame t.1.unop.left.inner).augmentation
    (ResolutionLiftSpace.frame Y.inner).augmentation a.map.diagram a.frame a.over
    (ResolutionLiftSpace.baseMap t.1.unop.left.inner W (a.map.base ≫ g))
    (ResolutionLiftSpace.baseMap Y.inner W g) hb
  change (LiftSpace.point (ResolutionLiftSpace.frame Y.inner).obj
    (ResolutionLiftSpace.frame Y.inner).augmentation (ResolutionLiftSpace.baseMap Y.inner W g) ≫
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHomMap a.frame).app ((Functor.const SimplexCategory).obj W.base)) ≫
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom (ResolutionLiftSpace.frame t.1.unop.left.inner).obj).map
      ((Functor.const SimplexCategory).map t.2.hom.base) = _
  rw [hp, LiftSpace.point_postcomp]
  congr 1
  simp only [ResolutionLiftSpace.baseMap, total, Functor.map_comp, Category.assoc, a]

abbrev fibers : Context Y W ⥤ SSet.{v} := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.FiberFunctor.functor (rawProjection Y W) (basepoint Y W g)

/-- This is the original actual resolution lift space over the transported base map. -/
def fiberIso (t : Context Y W) : (fibers Y W g).obj t ≅
    ResolutionLiftSpace.obj t.1.unop.left.inner t.2.right (total Y W g t) :=
  pullback.congrHom rfl (basepoint_eq Y W g t)

@[reassoc (attr := simp)]
lemma fiberIso_projection (t : Context Y W) :
    (fiberIso Y W g t).hom ≫
      ResolutionLiftSpace.projection t.1.unop.left.inner t.2.right (total Y W g t) =
        (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.FiberFunctor.projection (rawProjection Y W) (basepoint Y W g)).app t :=
  by
    change (pullback.congrHom
      (rfl : (rawProjection Y W).app t = (rawProjection Y W).app t)
      (basepoint_eq Y W g t)).hom ≫ pullback.snd _ _ = pullback.snd _ _
    simp [pullback.congrHom_hom, pullback.map]

abbrev rootInclusion : ResolutionLiftSpace.obj Y.inner W g ⟶
    (rawPairs (C := C)).obj (Opposite.op Y, W) :=
  ResolutionLiftSpace.inclusion Y.inner W g

/-- Every actual root lift is transported simultaneously through all contexts. -/
def rawFamily : (Functor.const (Context Y W)).obj (ResolutionLiftSpace.obj Y.inner W g) ⟶
    raw Y W :=
  (Functor.const (Context Y W)).map (rootInclusion Y W g) ≫ rootCone Y W rawPairs

lemma rawFamily_over (t : Context Y W) :
    (rawFamily Y W g).app t ≫ (rawProjection Y W).app t =
      SSet.stdSimplex.isTerminalObj₀.from (ResolutionLiftSpace.obj Y.inner W g) ≫
        (basepoint Y W g).app t := by
  change (rootInclusion Y W g ≫ rawPairs.map (rootMap Y W t)) ≫
    pairProjection.app ((contexts Y W).obj t) =
      _ ≫ (rootPoint Y W g ≫ basePairs.map (rootMap Y W t))
  rw [Category.assoc, pairProjection.naturality, ← Category.assoc]
  have h : rootInclusion Y W g ≫ pairProjection.app (Opposite.op Y, W) =
      ResolutionLiftSpace.projection Y.inner W g ≫ rootPoint Y W g :=
    pullback.condition
  rw [h, Category.assoc]
  congr 1
  exact SSet.stdSimplex.isTerminalObj₀.hom_ext _ _

/-- A natural family of all transported root lifts, with its actual fiber target. -/
def family : (Functor.const (Context Y W)).obj (ResolutionLiftSpace.obj Y.inner W g) ⟶
    fibers Y W g :=
  _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.FiberFunctor.liftFamily (rawProjection Y W) (basepoint Y W g)
    (rawFamily Y W g) (rawFamily_over Y W g)

/-- Both orders of changing the two contexts give the same actual fiber map. -/
lemma fibers_interchange {a b : (Over Y)ᵒᵖ} {c d : Under W}
    (k : a ⟶ b) (l : c ⟶ d) :
    (fibers Y W g).map (show (a, c) ⟶ (b, c) from (k, 𝟙 c)) ≫
      (fibers Y W g).map (show (b, c) ⟶ (b, d) from (𝟙 b, l)) =
      (fibers Y W g).map (show (a, c) ⟶ (a, d) from (𝟙 a, l)) ≫
      (fibers Y W g).map (show (a, d) ⟶ (b, d) from (k, 𝟙 d)) := by
  rw [← Functor.map_comp, ← Functor.map_comp]
  congr 1
  apply Prod.ext <;> simp

variable [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)

/-- The original interpolation transported naturally through both variables. -/
def leftFamily : (Functor.const (Context Y W)).obj (CoherentLiftTuples.obj Y.inner W g) ⟶
    fibers Y W g :=
  (Functor.const (Context Y W)).map (CoherentLiftTuples.interpolation hcof Y.inner W g) ≫
    family Y W g

/-- All strict lift vertices are retained as one natural boundary. -/
def boundary : (Functor.const (Context Y W)).obj (vertices Y.inner W g) ⟶ fibers Y W g :=
  (Functor.const (Context Y W)).map (vertexInclusion Y.inner W g) ≫ leftFamily Y W g hcof

def functor : Context Y W ⥤ SSet.{v} :=
  RelativeChoiceFunctor.functor (fibers Y W g) (vertexInclusion Y.inner W g)
    (boundary Y W g hcof)

def projection : functor Y W g hcof ⟶ (Functor.const (Context Y W)).obj
    (SSet.stdSimplex.{v}.obj (SimplexCategory.mk 0)) :=
  RelativeChoiceFunctor.projection (fibers Y W g) (vertexInclusion Y.inner W g)
    (boundary Y W g hcof)

/-- One strictly natural point preserving the entire specified vertex family. -/
def point : (Functor.const (Context Y W)).obj
    (SSet.stdSimplex.{v}.obj (SimplexCategory.mk 0)) ⟶ functor Y W g hcof :=
  RelativeChoiceFunctor.point (fibers Y W g) (vertexInclusion Y.inner W g)
    (boundary Y W g hcof) (leftFamily Y W g hcof) (fun _ => rfl)

lemma point_projection : point Y W g hcof ≫ projection Y W g hcof = 𝟙 _ :=
  RelativeChoiceFunctor.point_projection (fibers Y W g) (vertexInclusion Y.inner W g)
    (boundary Y W g hcof) (leftFamily Y W g hcof) (fun _ => rfl)

lemma interchange {a b : (Over Y)ᵒᵖ} {c d : Under W} (k : a ⟶ b) (l : c ⟶ d) :
    (functor Y W g hcof).map (show (a, c) ⟶ (b, c) from (k, 𝟙 c)) ≫
      (functor Y W g hcof).map (show (b, c) ⟶ (b, d) from (𝟙 b, l)) =
      (functor Y W g hcof).map (show (a, c) ⟶ (a, d) from (𝟙 a, l)) ≫
      (functor Y W g hcof).map (show (a, d) ⟶ (b, d) from (k, 𝟙 d)) := by
  rw [← Functor.map_comp, ← Functor.map_comp]
  congr 1
  apply Prod.ext <;> simp

include hcof in
lemma fiber_projection_trivialFibration (t : Context Y W) :
    trivialFibrations SSet.{v}
      ((_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.FiberFunctor.projection (rawProjection Y W) (basepoint Y W g)).app t) := by
  rw [← fiberIso_projection]
  exact (trivialFibrations SSet.{v}).comp_mem _ _
    ((trivialFibrations SSet.{v}).of_isIso (fiberIso Y W g t).hom)
    (ResolutionLiftSpace.projection_trivialFibration hcof _ _ _)

lemma projection_trivialFibration
    (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp) (t : Context Y W) :
    trivialFibrations SSet.{v} ((projection Y W g hcof).app t) :=
  _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.projection_trivialFibration hcof hfib (vertexInclusion Y.inner W g)
    ((boundary Y W g hcof).app t)
    ((_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.FiberFunctor.projection (rawProjection Y W) (basepoint Y W g)).app t)
    (fiber_projection_trivialFibration Y W g hcof t)

lemma point_weakEquivalence
    (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp) (t : Context Y W) :
    weakEquivalences SSet.{v} ((point Y W g hcof).app t) := by
  have hp := projection_trivialFibration Y W g hcof hfib t
  have he : (point Y W g hcof).app t ≫ (projection Y W g hcof).app t = 𝟙 _ :=
    congr_app (point_projection Y W g hcof) t
  exact (weakEquivalences SSet.{v}).of_postcomp _ _ hp.2
    (he.symm ▸ (weakEquivalences SSet.{v}).id_mem _)

end SerrePositivity.HomotopyFunctionComplex.MixedChoiceFunctor
