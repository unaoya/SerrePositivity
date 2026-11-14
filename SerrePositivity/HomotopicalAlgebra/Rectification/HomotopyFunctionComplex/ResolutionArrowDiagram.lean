module

public import SerrePositivity.HomotopicalAlgebra.Rectification.CategoryTheory.ArrowContext
public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.MixedChoiceFunctor
public import SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.NerveFillerExtension
public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.Pullbacks.FiberFunctorReindex
public import SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.NerveCoherentReindex

/-!
# 中断した任意モデル源への一般化：ResolutionArrowDiagram

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：One small lift-space diagram for all central base arrows at once。

## 方針（定義・証明）
frameによる導来写像空間と整合図式の厳密化に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0282][inventory]を参照する。

[inventory]: ../../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0282
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# One small lift-space diagram for all central base arrows at once

The central arrow is part of the category of elements of the actual base
Hom bifunctor. Its tautological point is natural before taking fibers.
Thus changing both endpoints and the central arrow gives strict maps of
the actual lift spaces, with no choice of a functorial resolution lift.
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SerrePositivity.SimplicialModel

namespace SerrePositivity.HomotopyFunctionComplex.ResolutionArrowDiagram
variable (C : Type u) [Category.{v} C] [ModelCategory C]
local instance : ModelCategory (SimplexCategory ⥤ C) := Reedy.simplexModelCategory C

abbrev pairs := (FramedResolution C)ᵒᵖ × ResolutionObject C
abbrev bases : pairs C ⥤ Cᵒᵖ × C := FramedResolution.projection.op.prod ResolutionObject.projection
abbrev baseMaps : pairs C ⥤ Type v := bases C ⋙ ArrowContext.homs C
abbrev Index := (baseMaps C).Elements
abbrev forget : Index C ⥤ pairs C := Functor.Elements.π (baseMaps C)
abbrev baseIndex : Index C ⥤ ArrowContext.Index C :=
  Functor.Elements.precomp (bases C) (ArrowContext.homs C)

abbrev source (q : Index C) : FramedResolution C := q.obj.1.unop
abbrev target (q : Index C) : ResolutionObject C := q.obj.2
abbrev arrow (q : Index C) : (source C q).inner.base ⟶ (target C q).base := q.val

lemma equation {q r : Index C} (f : q ⟶ r) :
    (f.hom.1.unop.map.base ≫ arrow C q) ≫ f.hom.2.base = arrow C r := f.map_val

abbrev raw : Index C ⥤ SSet.{v} := forget C ⋙ MixedChoiceFunctor.rawPairs
abbrev base : Index C ⥤ SSet.{v} := forget C ⋙ MixedChoiceFunctor.basePairs
abbrev rawProjection : raw C ⟶ base C :=
  Functor.whiskerLeft (forget C) MixedChoiceFunctor.pairProjection

/-- The tautological center is a natural point in the base simplicial diagram. -/
def basepoint : (Functor.const (Index C)).obj
    (SSet.stdSimplex.{v}.obj (SimplexCategory.mk 0)) ⟶ base C where
  app q := MixedChoiceFunctor.rootPoint (source C q) (target C q) (arrow C q)
  naturality {q r} f := by
    change (𝟙 _) ≫ MixedChoiceFunctor.rootPoint (source C r) (target C r) (arrow C r) =
      MixedChoiceFunctor.rootPoint (source C q) (target C q) (arrow C q) ≫
        MixedChoiceFunctor.basePairs.map f.hom
    rw [Category.id_comp]
    have h := MixedChoiceFunctor.basepoint_eq (source C q) (target C q) (arrow C q)
      (Opposite.op (Over.mk f.hom.1.unop), Under.mk f.hom.2)
    change MixedChoiceFunctor.rootPoint (source C q) (target C q) (arrow C q) ≫
        MixedChoiceFunctor.basePairs.map f.hom =
      MixedChoiceFunctor.rootPoint (source C r) (target C r)
        (f.hom.1.unop.map.base ≫ arrow C q ≫ f.hom.2.base) at h
    rw [← Category.assoc, equation C f] at h
    exact h.symm

/-- Small actual fibers for every framed source, target resolution and center simultaneously. -/
abbrev fibers : Index C ⥤ SSet.{v} := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.FiberFunctor.functor (rawProjection C) (basepoint C)

/-- No change of coordinates is needed at an object: this is the original lift space. -/
def fiberIso (q : Index C) : (fibers C).obj q ≅
    ResolutionLiftSpace.obj (source C q).inner (target C q) (arrow C q) := Iso.refl _

@[reassoc (attr := simp)]
lemma fiberIso_inclusion (q : Index C) : (fiberIso C q).hom ≫
    ResolutionLiftSpace.inclusion (source C q).inner (target C q) (arrow C q) =
      (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.FiberFunctor.inclusion (rawProjection C) (basepoint C)).app q := Category.id_comp _

@[reassoc (attr := simp)]
lemma fiberIso_projection (q : Index C) : (fiberIso C q).hom ≫
    ResolutionLiftSpace.projection (source C q).inner (target C q) (arrow C q) =
      (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.FiberFunctor.projection (rawProjection C) (basepoint C)).app q := Category.id_comp _

/-- The universal lift maps cover the actual raw frame/target transport. -/
@[reassoc]
lemma map_inclusion {q r : Index C} (f : q ⟶ r) :
    (fibers C).map f ≫ (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.FiberFunctor.inclusion (rawProjection C) (basepoint C)).app r =
      (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.FiberFunctor.inclusion (rawProjection C) (basepoint C)).app q ≫
        MixedChoiceFunctor.rawPairs.map f.hom := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.FiberFunctor.map_fst _ _ f

/-- Embed every fixed-center external context in the universal changing-center index. -/
def fromContext (X : FramedResolution C) (W : ResolutionObject C) (g : X.inner.base ⟶ W.base) :
    MixedChoiceFunctor.Context X W ⥤ Index C where
  obj t := (baseMaps C).elementsMk ((MixedChoiceFunctor.contexts X W).obj t)
    ((baseMaps C).map (MixedChoiceFunctor.rootMap X W t) g)
  map {s t} k :=
    { hom := (MixedChoiceFunctor.contexts X W).map k
      map_val := by
        change (baseMaps C).map ((MixedChoiceFunctor.contexts X W).map k)
          ((baseMaps C).map (MixedChoiceFunctor.rootMap X W s) g) = _
        rw [← Functor.map_comp_apply, MixedChoiceFunctor.rootMap_naturality] }

lemma fromContext_arrow (X : FramedResolution C) (W : ResolutionObject C)
    (g : X.inner.base ⟶ W.base) (t : MixedChoiceFunctor.Context X W) :
    arrow C ((fromContext C X W g).obj t) = MixedChoiceFunctor.total X W g t :=
  Category.assoc _ _ _

lemma fromContext_basepoint (X : FramedResolution C) (W : ResolutionObject C)
    (g : X.inner.base ⟶ W.base) :
    Functor.whiskerLeft (fromContext C X W g) (basepoint C) =
      MixedChoiceFunctor.basepoint X W g := by
  apply NatTrans.ext
  funext t
  change MixedChoiceFunctor.rootPoint t.1.unop.left t.2.right
    (arrow C ((fromContext C X W g).obj t)) = (MixedChoiceFunctor.basepoint X W g).app t
  rw [fromContext_arrow]
  exact (MixedChoiceFunctor.basepoint_eq X W g t).symm

/-- Recover the old fixed-center fiber diagram as a natural restriction of the universal one. -/
def fromContextIso (X : FramedResolution C) (W : ResolutionObject C)
    (g : X.inner.base ⟶ W.base) :
    fromContext C X W g ⋙ fibers C ≅ MixedChoiceFunctor.fibers X W g :=
  _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.FiberFunctorReindex.reindex (rawProjection C) (basepoint C) (fromContext C X W g) ≪≫
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.FiberFunctorReindex.congrPoint _ _ _ (fromContext_basepoint C X W g)

/-- Any actual strict lift can still be prescribed as the original point. -/
def selectedPoint (q : Index C) : SSet.stdSimplex.{v}.obj (SimplexCategory.mk 0) ⟶
    (fibers C).obj q :=
  ResolutionLiftSpace.ofLift (ResolutionObject.lift (arrow C q))

variable [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)

include hcof in
lemma projection_trivialFibration (q : Index C) : trivialFibrations SSet.{v}
    ((_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.FiberFunctor.projection (rawProjection C) (basepoint C)).app q) :=
  ResolutionLiftSpace.projection_trivialFibration hcof _ _ _

include hcof in
lemma fillers (q : Index C) : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.BoundaryFillers ((fibers C).obj q) :=
  fun n a => ResolutionLiftSpace.extension hcof _ _ _ (SSet.boundary n).ι a

/-- One whole coherent choice for all centers, retaining every given independent lift point. -/
def coherent (points : ∀ q, SSet.stdSimplex.{v}.obj (SimplexCategory.mk 0) ⟶ (fibers C).obj q) :
    NerveCoherentFamily.System (fibers C) :=
  NerveFillerExtension.extendVertices (fibers C) (fillers C hcof) points

lemma coherent_point
    (points : ∀ q, SSet.stdSimplex.{v}.obj (SimplexCategory.mk 0) ⟶ (fibers C).obj q)
    (q : Index C) :
    (coherent C hcof points).app (NerveSimplexEndpoint.ofChain (ComposableArrows.mk₀ q)) =
      points q := NerveFillerExtension.extendVertices_point _ _ _ q

/-- In particular, all independently selected strict resolution lifts are retained. -/
abbrev selectedSystem := coherent C hcof (selectedPoint C)

lemma selectedSystem_point (q : Index C) :
    (selectedSystem C hcof).app (NerveSimplexEndpoint.ofChain (ComposableArrows.mk₀ q)) =
      ResolutionLiftSpace.ofLift (ResolutionObject.lift (arrow C q)) :=
  coherent_point C hcof _ q

/-- A fixed-center system obtained by restriction of the one universal whole system. -/
def coherentContext
    (points : ∀ q, SSet.stdSimplex.{v}.obj (SimplexCategory.mk 0) ⟶ (fibers C).obj q)
    (X : FramedResolution C) (W : ResolutionObject C) (g : X.inner.base ⟶ W.base) :
    NerveCoherentFamily.System (MixedChoiceFunctor.fibers X W g) :=
  NerveCoherentFamily.map _ (fromContextIso C X W g).hom
    (NerveCoherentReindex.reindex (fromContext C X W g) (fibers C) (coherent C hcof points))

lemma coherentContext_component
    (points : ∀ q, SSet.stdSimplex.{v}.obj (SimplexCategory.mk 0) ⟶ (fibers C).obj q)
    (X : FramedResolution C) (W : ResolutionObject C) (g : X.inner.base ⟶ W.base)
    (s : NerveSimplexEndpoint.Index (MixedChoiceFunctor.Context X W)) :
    (coherentContext C hcof points X W g).app s =
      (coherent C hcof points).app ((NerveCoherentReindex.index (fromContext C X W g)).obj s) ≫
        (fromContextIso C X W g).hom.app (NerveSimplexEndpoint.endpoint s) := rfl

end SerrePositivity.HomotopyFunctionComplex.ResolutionArrowDiagram
