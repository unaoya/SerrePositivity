module

public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.ResolutionArrowComparisonEndpoints

/-!
# 中断した任意モデル源への一般化：ResolutionArrowElementary

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：The original pre/postcomparison endpoints inside the all-center arrow system。

## 方針（定義・証明）
frameによる導来写像空間と整合図式の厳密化に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0283][inventory]を参照する。

[inventory]: ../../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0283
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# The original pre/postcomparison endpoints inside the all-center arrow system
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SerrePositivity.SimplicialModel SerrePositivity.HomotopyFunctionComplex
open ResolutionArrowDiagram ResolutionArrowTuples

namespace SerrePositivity.HomotopyFunctionComplex.ResolutionArrowElementary
variable {C : Type u} [Category.{v} C] [ModelCategory C]
local instance : ModelCategory (SimplexCategory ⥤ C) := Reedy.simplexModelCategory C

abbrev center (X : FramedResolution C) (Y : ResolutionObject C) (f : X.inner.base ⟶ Y.base) :
    Index C := (baseMaps C).elementsMk (Opposite.op X, Y) f

def post (X : FramedResolution C) (Y W : ResolutionObject C) (f : X.inner.base ⟶ Y.base)
    (g : Y ⟶ W) : center X Y f ⟶ center X W (f ≫ g.base) where
  hom := (𝟙 _, g)
  map_val := by
    change ((𝟙 _) ≫ f) ≫ g.base = f ≫ g.base
    rw [Category.id_comp]

def pre (X Y : FramedResolution C) (W : ResolutionObject C) (f : X ⟶ Y)
    (g : Y.inner.base ⟶ W.base) : center Y W g ⟶ center X W (f.map.base ≫ g) where
  hom := (f.op, 𝟙 _)
  map_val := by
    change (f.map.base ≫ g) ≫ (𝟙 _) = f.map.base ≫ g
    exact Category.comp_id _

lemma post_fibers (X : FramedResolution C) (Y W : ResolutionObject C)
    (f : X.inner.base ⟶ Y.base) (g : Y ⟶ W) :
    (fibers C).map (post X Y W f g) = ResolutionLiftPostcomposition.map X.inner Y W f g := by
  apply ResolutionLiftSpace.hom_ext
  · apply (map_inclusion C (post X Y W f g)).trans
    apply Eq.trans ?_ (ResolutionLiftPostcomposition.map_inclusion X.inner Y W f g).symm
    change _ ≫ ((MixedChoiceFunctor.rawBifunctor.map (𝟙 _)).app Y.resolution.obj ≫
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom (ResolutionLiftSpace.frame X.inner).obj).map g.diagram) = _
    rw [CategoryTheory.Functor.map_id]
    exact congrArg (fun k => ResolutionLiftSpace.inclusion X.inner Y f ≫ k)
      (Category.id_comp _)
  · exact SSet.stdSimplex.isTerminalObj₀.hom_ext _ _

lemma pre_fibers (X Y : FramedResolution C) (W : ResolutionObject C) (f : X ⟶ Y)
    (g : Y.inner.base ⟶ W.base) : (fibers C).map (pre X Y W f g) =
      ResolutionLiftPrecomposition.map X.inner Y.inner W f.map g (FramedResolution.frameMap f) := by
  apply ResolutionLiftSpace.hom_ext
  · apply (map_inclusion C (pre X Y W f g)).trans
    apply Eq.trans ?_ (LiftSpacePrecomposition.map_inclusion _ _ _ _ _ _ _ _ _ _ _).symm
    change _ ≫ ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHomMap f.frame).app W.resolution.obj ≫
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom (ResolutionLiftSpace.frame X.inner).obj).map (𝟙 W.resolution.obj)) = _
    rw [CategoryTheory.Functor.map_id]
    exact congrArg (fun k => ResolutionLiftSpace.inclusion Y.inner W g ≫ k)
      (Category.comp_id _)
  · exact SSet.stdSimplex.isTerminalObj₀.hom_ext _ _

lemma post_tuples (X : FramedResolution C) (Y W : ResolutionObject C)
    (f : X.inner.base ⟶ Y.base) (g : Y ⟶ W) : (tuples C).map (post X Y W f g) =
      _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.VertexTuples.map (CoherentLiftRelative.postStrict X.inner Y W f g) := by
  apply congrArg _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.VertexTuples.map
  funext k
  apply Subtype.ext
  exact Category.id_comp _

lemma pre_tuples (X Y : FramedResolution C) (W : ResolutionObject C) (f : X ⟶ Y)
    (g : Y.inner.base ⟶ W.base) : (tuples C).map (pre X Y W f g) =
      _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.VertexTuples.map (CoherentLiftRelative.preStrict X.inner Y.inner W f.map g) := by
  apply congrArg _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.VertexTuples.map
  funext k
  apply Subtype.ext
  exact congrArg (fun k => f.map ≫ k) (Category.comp_id _)

variable [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
open ResolutionArrowComparisonEndpoints

lemma post_left (X : FramedResolution C) (Y W : ResolutionObject C)
    (f : X.inner.base ⟶ Y.base) (g : Y ⟶ W) : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.lower
    (NerveMovingParameter.evaluate (parameter C) (values C)
      (left C hcof) (Arrow.mk (post X Y W f g))) =
    CoherentLiftRelative.postLeft hcof X.inner Y W f g := by
  exact (left_recover C hcof (Arrow.mk (post X Y W f g))).trans
    (congrArg (fun k => CoherentLiftTuples.interpolation hcof X.inner Y f ≫ k)
      (post_fibers X Y W f g))

lemma post_right (X : FramedResolution C) (Y W : ResolutionObject C)
    (f : X.inner.base ⟶ Y.base) (g : Y ⟶ W) : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.lower
    (NerveMovingParameter.evaluate (parameter C) (values C)
      (right C hcof) (Arrow.mk (post X Y W f g))) =
    CoherentLiftRelative.postRight hcof X.inner Y W f g := by
  exact (right_recover C hcof (Arrow.mk (post X Y W f g))).trans
    (congrArg (fun k => k ≫ CoherentLiftTuples.interpolation hcof X.inner W (f ≫ g.base))
      (post_tuples X Y W f g))

lemma pre_left (X Y : FramedResolution C) (W : ResolutionObject C) (f : X ⟶ Y)
    (g : Y.inner.base ⟶ W.base) : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.lower
    (NerveMovingParameter.evaluate (parameter C) (values C)
      (left C hcof) (Arrow.mk (pre X Y W f g))) =
    CoherentLiftRelative.preLeft hcof X.inner Y.inner W f.map g (FramedResolution.frameMap f) := by
  exact (left_recover C hcof (Arrow.mk (pre X Y W f g))).trans
    (congrArg (fun k => CoherentLiftTuples.interpolation hcof Y.inner W g ≫ k)
      (pre_fibers X Y W f g))

lemma pre_right (X Y : FramedResolution C) (W : ResolutionObject C) (f : X ⟶ Y)
    (g : Y.inner.base ⟶ W.base) : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.lower
    (NerveMovingParameter.evaluate (parameter C) (values C)
      (right C hcof) (Arrow.mk (pre X Y W f g))) =
    CoherentLiftRelative.preRight hcof X.inner Y.inner W f.map g := by
  exact (right_recover C hcof (Arrow.mk (pre X Y W f g))).trans
    (congrArg (fun k => k ≫ CoherentLiftTuples.interpolation hcof X.inner W (f.map.base ≫ g))
      (pre_tuples X Y W f g))

end SerrePositivity.HomotopyFunctionComplex.ResolutionArrowElementary
