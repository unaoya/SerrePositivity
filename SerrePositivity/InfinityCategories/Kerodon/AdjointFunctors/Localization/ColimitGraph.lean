module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Diagram
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.Types.Colimits

/-!
# 全語の hammock graph の実際の余極限

概要：全語の図式の単体集合としての余極限と元の標準射を構成する。
方針：全語の厳密な図式に presheaf 圏の余極限を適用する。
規約：縮約 hammock との同型・弱同値性は後続。余極限の普遍性はここで証明済み。
使われ方：固定語の graph から hammock 局所化への比較と合成。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] (W : MorphismProperty C) [W.IsMultiplicative] (X Y : C)

/-- 全語の元の hammock graph の図式の単体集合としての余極限。 -/
def colimitGraph : SSet.{max u v} := colimit (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Diagram.graphDiagram W X Y)

/-- 元の各固定語の graph から全語の余極限への実際の標準射。 -/
def graphInclusion (w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph W w X Y ⟶ colimitGraph W X Y :=
  colimit.ι (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Diagram.graphDiagram W X Y) w

/-- 元の列の圧縮と恒等列の挿入は、同じ余極限の標準射と可換。 -/
lemma graphInclusion_naturality {a b : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} (f : a ⟶ b) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Diagram.graphDiagram W X Y).map f ≫ graphInclusion W X Y b = graphInclusion W X Y a :=
  colimit.w (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Diagram.graphDiagram W X Y) f

/-- 同じ元の図式の cocone は、実際に余極限となる。 -/
def colimitGraph_isColimit : IsColimit (colimit.cocone (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Diagram.graphDiagram W X Y)) :=
  colimit.isColimit _

/-- 全固定語上で整合する射の族から、元の余極限上の射を構成する。 -/
def colimitGraphDesc {Z : SSet.{max u v}} (α : ∀ w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph W w X Y ⟶ Z)
    (hα : ∀ {a b : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} (f : a ⟶ b), (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Diagram.graphDiagram W X Y).map f ≫ α b = α a) :
    colimitGraph W X Y ⟶ Z :=
  colimit.desc (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Diagram.graphDiagram W X Y)
    { pt := Z
      ι :=
        { app := α
          naturality _ _ f := (hα f).trans (Category.comp_id (α _)).symm } }

@[simp] lemma graphInclusion_desc {Z : SSet.{max u v}} (α : ∀ w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph W w X Y ⟶ Z)
    (hα : ∀ {a b : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} (f : a ⟶ b), (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Diagram.graphDiagram W X Y).map f ≫ α b = α a) (w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) :
    graphInclusion W X Y w ≫ colimitGraphDesc W X Y α hα = α w :=
  colimit.ι_desc _ _

/-- 全固定語の元の標準射上での一致は、余極限からの射の一致を与える。 -/
lemma colimitGraph_hom_ext {Z : SSet.{max u v}} (f g : colimitGraph W X Y ⟶ Z)
    (h : ∀ w, graphInclusion W X Y w ≫ f = graphInclusion W X Y w ≫ g) : f = g :=
  colimit.hom_ext h

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
