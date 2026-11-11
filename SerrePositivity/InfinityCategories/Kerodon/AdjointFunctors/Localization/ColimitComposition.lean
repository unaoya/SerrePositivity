module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.CompositionPairing
public import Mathlib.CategoryTheory.Monoidal.Limits.Colimits
public import Mathlib.CategoryTheory.Monoidal.Limits.Preserves
public import Mathlib.CategoryTheory.Monoidal.Closed.FunctorToTypes

/-!
# 二つの元の hammock 余極限の積からの合成

概要：元の全語の余極限の積から、元の合成余錐によって合成を構成する。
方針：外部積の余錐の余極限性を IsColimit.tensor₂ で得て、同じ合成余錐へ降下。
規約：添字圏の filtered 性や単体集合のモデル構造は仮定しない。
使われ方：hammock の元の豊穣合成と結合・単位則の検証。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory CategoryTheory.Limits MonoidalCategory

variable {C : Type u} [Category.{v} C] (W : MorphismProperty C) [W.IsMultiplicative] (X Y Z : C)

/-- 二つの元の全語の標準余錐の外部積。 -/
def tensorPairCocone : Cocone (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.pairDiagram W X Y Z) :=
  (colimit.cocone (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Diagram.graphDiagram W X Y)).tensor₂ (colimit.cocone (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Diagram.graphDiagram W Y Z))

/-- 積の各変数の余極限保存から、元の外部積余錐の余極限性を得る。 -/
def tensorPairCocone_isColimit : IsColimit (tensorPairCocone W X Y Z) :=
  IsColimit.tensor₂ (colimit.isColimit (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Diagram.graphDiagram W X Y))
    (colimit.isColimit (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Diagram.graphDiagram W Y Z))

/-- 外部積余錐の成分は、元の二つの標準射の積そのもの。 -/
lemma tensorPairCocone_ι (a b : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) :
    (tensorPairCocone W X Y Z).ι.app (a, b) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphInclusion W X Y a ⊗ₘ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphInclusion W Y Z b) := by
  simp only [tensorPairCocone, Cocone.tensor₂, Functor.mapCocone₂,
    Functor.const_obj_obj, curriedTensor_map_app, curriedTensor_obj_map,
    colimit.cocone_x, colimit.cocone_ι, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Diagram.graphDiagram_obj,
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphInclusion, tensorHom_def]

/-- 対の図式の余極限と、二つの元の余極限の積との標準同型。 -/
def tensorPairColimitIso :
    colimit (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.pairDiagram W X Y Z) ≅ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph W X Y ⊗ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph W Y Z :=
  (colimit.isColimit (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.pairDiagram W X Y Z)).coconePointUniqueUpToIso
    (tensorPairCocone_isColimit W X Y Z)

/-- 標準同型は元の全固定語の二つの標準射の積を回収する。 -/
lemma tensorPairColimitIso_fac (a b : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) :
    colimit.ι (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.pairDiagram W X Y Z) (a, b) ≫ (tensorPairColimitIso W X Y Z).hom =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphInclusion W X Y a ⊗ₘ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphInclusion W Y Z b) := by
  simpa only [tensorPairColimitIso, colimit.cocone_ι, tensorPairCocone_ι] using
    (colimit.isColimit (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.pairDiagram W X Y Z)).comp_coconePointUniqueUpToIso_hom
      (tensorPairCocone_isColimit W X Y Z) (a, b)

/-- 二つの実際の余極限の積から、元の合成余錐により定める合成。 -/
def colimitComposition : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph W X Y ⊗ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph W Y Z ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph W X Z :=
  (tensorPairCocone_isColimit W X Y Z).desc (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.compositionPairingCocone W X Y Z)

/-- 元の全固定語の対で、元の合成と同じ標準射を厳密に回収する。 -/
lemma colimitComposition_fac (a b : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphInclusion W X Y a ⊗ₘ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphInclusion W Y Z b) ≫ colimitComposition W X Y Z =
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphPairing W X Y Z a b := by
  have h := (tensorPairCocone_isColimit W X Y Z).fac (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.compositionPairingCocone W X Y Z) (a, b)
  simpa only [tensorPairCocone_ι, colimitComposition, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.compositionPairingCocone] using h

/-- 前工程の対の余極限からの比較は、標準同型と同じ合成の積。 -/
lemma tensorPairColimitIso_comp :
    (tensorPairColimitIso W X Y Z).hom ≫ colimitComposition W X Y Z =
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitCompositionPairing W X Y Z :=
  (colimit.isColimit (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.pairDiagram W X Y Z)).coconePointUniqueUpToIso_hom_desc
    (tensorPairCocone_isColimit W X Y Z)

/-- 全固定語の元の標準射の積上での一致は、元の余極限の積からの射の一致を与える。 -/
lemma tensorPair_hom_ext {K : SSet.{max u v}}
    (f g : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph W X Y ⊗ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph W Y Z ⟶ K)
    (h : ∀ a b : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word, (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphInclusion W X Y a ⊗ₘ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphInclusion W Y Z b) ≫ f =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphInclusion W X Y a ⊗ₘ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphInclusion W Y Z b) ≫ g) : f = g := by
  apply (tensorPairCocone_isColimit W X Y Z).hom_ext
  rintro ⟨a, b⟩
  simpa only [tensorPairCocone_ι] using h a b

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
