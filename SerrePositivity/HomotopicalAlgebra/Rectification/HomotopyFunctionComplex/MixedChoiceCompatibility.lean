module

public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.MixedChoiceFunctor
public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.CoherentLiftMixedComparison
public import SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.RelativeChoiceIso

/-!
# 中断した任意モデル源への一般化：MixedChoiceCompatibility

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：The mixed context diagram retains the original actual mixed comparisons。

## 方針（定義・証明）
自明fibrationのファイバーと相対延長による選択の比較に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0116][inventory]を参照する。

[inventory]: ../../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0116
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# The mixed context diagram retains the original actual mixed comparisons

The root family agrees with actual postcomposition followed by actual
precomposition. Its choice space is isomorphic to the original mixed
space, retaining the original interpolation, arbitrary parameter families
and all their faces. No independent comparison is substituted.
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
variable (Y : FramedResolution C) (W : ResolutionObject C) (g : Y.inner.base ⟶ W.base)

@[reassoc (attr := simp)]
lemma fiberIso_inclusion (t : Context Y W) :
    (fiberIso Y W g t).hom ≫
      ResolutionLiftSpace.inclusion t.1.unop.left.inner t.2.right (total Y W g t) =
        (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.FiberFunctor.inclusion (rawProjection Y W) (basepoint Y W g)).app t := by
  change (pullback.congrHom
    (rfl : (rawProjection Y W).app t = (rawProjection Y W).app t)
    (basepoint_eq Y W g t)).hom ≫ pullback.fst _ _ = pullback.fst _ _
  simp [pullback.congrHom_hom, pullback.map]

/-- The contextual root transport is the original post-then-pre map. -/
lemma family_existing (t : Context Y W) :
    (family Y W g).app t ≫ (fiberIso Y W g t).hom =
      ResolutionLiftPostcomposition.map Y.inner W t.2.right g t.2.hom ≫
        ResolutionLiftPrecomposition.map t.1.unop.left.inner Y.inner t.2.right
          t.1.unop.hom.map (g ≫ t.2.hom.base) (FramedResolution.frameMap t.1.unop.hom) := by
  apply ResolutionLiftSpace.hom_ext
  · rw [Category.assoc, fiberIso_inclusion]
    change (pullback.lift _ _ _ ≫ pullback.fst _ _) = _
    rw [pullback.lift_fst]
    change ResolutionLiftSpace.inclusion Y.inner W g ≫
      ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHomMap t.1.unop.hom.frame).app W.resolution.obj ≫
        (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom (ResolutionLiftSpace.frame t.1.unop.left.inner).obj).map
          t.2.hom.diagram) = _
    simp only [Category.assoc, ResolutionLiftSpace.pre_inclusion,
      ResolutionLiftSpace.post_inclusion_assoc]
    exact congrArg (fun q => ResolutionLiftSpace.inclusion Y.inner W g ≫ q)
      ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHomMap t.1.unop.hom.frame).naturality t.2.hom.diagram).symm
  · rw [Category.assoc, fiberIso_projection]
    change pullback.lift _ _ _ ≫ pullback.snd _ _ = _
    rw [pullback.lift_snd]
    exact SSet.stdSimplex.isTerminalObj₀.hom_ext _ _

variable [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)

lemma leftFamily_existing (t : Context Y W) :
    (leftFamily Y W g hcof).app t ≫ (fiberIso Y W g t).hom =
      CoherentLiftMixedComparison.familyA hcof t.1.unop.left.inner Y.inner W t.2.right
        t.1.unop.hom.map g t.2.hom (FramedResolution.frameMap t.1.unop.hom) := by
  change (CoherentLiftTuples.interpolation hcof Y.inner W g ≫ (family Y W g).app t) ≫ _ = _
  rw [Category.assoc, family_existing]
  rfl

include hcof in
lemma boundary_existing (t : Context Y W) :
    (boundary Y W g hcof).app t ≫ (fiberIso Y W g t).hom =
      CoherentLiftMixedComparison.boundary t.1.unop.left.inner Y.inner W t.2.right
        t.1.unop.hom.map g t.2.hom (FramedResolution.frameMap t.1.unop.hom) := by
  change (vertexInclusion Y.inner W g ≫ (leftFamily Y W g hcof).app t) ≫ _ = _
  rw [Category.assoc, leftFamily_existing]
  exact CoherentLiftMixedComparison.familyA_vertices hcof _ _ _ _ _ _ _ _

/-- An actual isomorphism with the old mixed space, including its fixed boundary. -/
def choiceIso (t : Context Y W) : (functor Y W g hcof).obj t ≅
    CoherentLiftMixedComparison.space t.1.unop.left.inner Y.inner W t.2.right
      t.1.unop.hom.map g t.2.hom (FramedResolution.frameMap t.1.unop.hom) :=
  RelativeChoiceSpace.postIso (vertexInclusion Y.inner W g) _ _ (fiberIso Y W g t)
    (boundary_existing Y W g hcof t)

lemma point_existing (t : Context Y W) :
    (point Y W g hcof).app t ≫ (choiceIso Y W g hcof t).hom =
      CoherentLiftMixedComparison.pointA hcof t.1.unop.left.inner Y.inner W t.2.right
        t.1.unop.hom.map g t.2.hom (FramedResolution.frameMap t.1.unop.hom) := by
  change RelativeChoiceSpace.ofExtension (vertexInclusion Y.inner W g)
    ((boundary Y W g hcof).app t) ((leftFamily Y W g hcof).app t) (by rfl) ≫
      (RelativeChoiceSpace.postIso (vertexInclusion Y.inner W g) _ _ (fiberIso Y W g t)
        (boundary_existing Y W g hcof t)).hom = _
  rw [RelativeChoiceSpace.postIso_ofExtension]
  exact RelativeChoiceSpace.ofExtension_congr _ _ _ _ _ _ (leftFamily_existing Y W g hcof t)

/-- The old mixed spaces themselves now form a strict diagram on all context arrows. -/
def existingFunctor : Context Y W ⥤ SSet.{v} where
  obj t := CoherentLiftMixedComparison.space t.1.unop.left.inner Y.inner W t.2.right
    t.1.unop.hom.map g t.2.hom (FramedResolution.frameMap t.1.unop.hom)
  map {s t} k := (choiceIso Y W g hcof s).inv ≫ (functor Y W g hcof).map k ≫
    (choiceIso Y W g hcof t).hom
  map_id t := by simp
  map_comp {s t r} k l := by
    change (choiceIso Y W g hcof s).inv ≫ (functor Y W g hcof).map (k ≫ l) ≫
        (choiceIso Y W g hcof r).hom =
      ((choiceIso Y W g hcof s).inv ≫ (functor Y W g hcof).map k ≫
        (choiceIso Y W g hcof t).hom) ≫ (choiceIso Y W g hcof t).inv ≫
          (functor Y W g hcof).map l ≫ (choiceIso Y W g hcof r).hom
    rw [Functor.map_comp]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]

/-- A natural isomorphism, rather than only unrelated component equivalences. -/
def existingIso : functor Y W g hcof ≅ existingFunctor Y W g hcof :=
  NatIso.ofComponents (choiceIso Y W g hcof) (by
    intro s t k
    change _ = _ ≫ ((choiceIso Y W g hcof s).inv ≫ _ ≫ _)
    simp)

/-- The old pointA is strictly natural throughout the mixed context diagram. -/
def existingPoint : (Functor.const (Context Y W)).obj
    (SSet.stdSimplex.{v}.obj (SimplexCategory.mk 0)) ⟶ existingFunctor Y W g hcof :=
  point Y W g hcof ≫ (existingIso Y W g hcof).hom

lemma existingPoint_component (t : Context Y W) : (existingPoint Y W g hcof).app t =
    CoherentLiftMixedComparison.pointA hcof t.1.unop.left.inner Y.inner W t.2.right
      t.1.unop.hom.map g t.2.hom (FramedResolution.frameMap t.1.unop.hom) :=
  point_existing Y W g hcof t

def existingProjection : existingFunctor Y W g hcof ⟶
    (Functor.const (Context Y W)).obj (SSet.stdSimplex.{v}.obj (SimplexCategory.mk 0)) :=
  (existingIso Y W g hcof).inv ≫ projection Y W g hcof

lemma existingProjection_component (t : Context Y W) :
    (existingProjection Y W g hcof).app t =
      RelativeChoiceSpace.projection (vertexInclusion Y.inner W g)
        (CoherentLiftMixedComparison.boundary t.1.unop.left.inner Y.inner W t.2.right
          t.1.unop.hom.map g t.2.hom (FramedResolution.frameMap t.1.unop.hom)) :=
  RelativeChoiceSpace.postIso_inv_projection _ _ _ _ (boundary_existing Y W g hcof t)

lemma existingPoint_projection : existingPoint Y W g hcof ≫
    existingProjection Y W g hcof = 𝟙 _ := by
  simp only [existingPoint, existingProjection, Category.assoc, Iso.hom_inv_id_assoc]
  exact point_projection Y W g hcof

/-- Retain any old parameter family, including independently selected comparison data. -/
abbrev retain (t : Context Y W) {K : SSet.{v}}
    (s : K ⟶ (existingFunctor Y W g hcof).obj t) : K ⟶ (functor Y W g hcof).obj t :=
  s ≫ (choiceIso Y W g hcof t).inv

@[reassoc (attr := simp)]
lemma retain_recover (t : Context Y W) {K : SSet.{v}}
    (s : K ⟶ (existingFunctor Y W g hcof).obj t) :
    retain Y W g hcof t s ≫ (choiceIso Y W g hcof t).hom = s := by
  simp [retain]

lemma retain_naturality (t : Context Y W) {K L : SSet.{v}} (j : K ⟶ L)
    (s : L ⟶ (existingFunctor Y W g hcof).obj t) :
    j ≫ retain Y W g hcof t s = retain Y W g hcof t (j ≫ s) :=
  (Category.assoc _ _ _).symm

lemma retain_family (t : Context Y W) {K : SSet.{v}}
    (s : K ⟶ (existingFunctor Y W g hcof).obj t) :
    RelativeChoiceSpace.family (vertexInclusion Y.inner W g) ((boundary Y W g hcof).app t)
        (retain Y W g hcof t s) =
      RelativeChoiceSpace.family (vertexInclusion Y.inner W g)
        (CoherentLiftMixedComparison.boundary t.1.unop.left.inner Y.inner W t.2.right
          t.1.unop.hom.map g t.2.hom (FramedResolution.frameMap t.1.unop.hom)) s ≫
            (fiberIso Y W g t).inv :=
  RelativeChoiceSpace.family_postIso_inv _ _ _ _ _ _

variable (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)

/-- The original chosen triangle is retained, with its original four-edge square data. -/
abbrev retainedTriangle (t : Context Y W) (left : Bool) :
    SSet.stdSimplex.{v}.obj (SimplexCategory.mk 2) ⟶ (functor Y W g hcof).obj t :=
  retain Y W g hcof t
    (CoherentLiftMixedComparison.triangle hcof hfib t.1.unop.left.inner Y.inner W t.2.right
      t.1.unop.hom.map g t.2.hom (FramedResolution.frameMap t.1.unop.hom) left)

lemma retainedTriangle_face (t : Context Y W) (left : Bool) (k : Fin 3) :
    SSet.stdSimplex.δ k ≫ retainedTriangle Y W g hcof hfib t left =
      retain Y W g hcof t
        ((CoherentLiftMixedComparison.data hcof hfib t.1.unop.left.inner Y.inner W t.2.right
          t.1.unop.hom.map g t.2.hom (FramedResolution.frameMap t.1.unop.hom) left).faces k) := by
  change _ ≫ (_ ≫ _) = _ ≫ _
  rw [← Category.assoc, CoherentLiftMixedComparison.triangle_face]

lemma retainedTriangle_shared_diagonal (t : Context Y W) :
    SSet.stdSimplex.δ (1 : Fin 3) ≫ retainedTriangle Y W g hcof hfib t true =
      SSet.stdSimplex.δ (1 : Fin 3) ≫ retainedTriangle Y W g hcof hfib t false := by
  change _ ≫ (_ ≫ _) = _ ≫ (_ ≫ _)
  rw [← Category.assoc, ← Category.assoc, CoherentLiftMixedComparison.shared_diagonal]

end SerrePositivity.HomotopyFunctionComplex.MixedChoiceFunctor
