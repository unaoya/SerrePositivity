module

public import SerrePositivity.EInfinity.Hammock.CompositionPairing
public import Mathlib.CategoryTheory.Monoidal.Limits.Colimits
public import Mathlib.CategoryTheory.Monoidal.Limits.Preserves
public import Mathlib.CategoryTheory.Monoidal.Closed.FunctorToTypes

/-!
# 二つの元の hammock 余極限の積からの合成

概要：元の全語の余極限の積から、元の合成余錐によって合成を構成する。
方針：外部積の余錐の余極限性を IsColimit.tensor₂ で得て、同じ合成余錐へ降下。
規約：添字圏の filtered 性や単体集合のモデル構造は仮定しない。
使われ方：hammock の元の豊穣合成と結合・単位則の検証。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.EInfinity.Hammock
open CategoryTheory CategoryTheory.Limits MonoidalCategory

variable {C : Type u} [Category.{v} C] (W : MorphismProperty C) [W.IsMultiplicative] (X Y Z : C)

/-- 二つの元の全語の標準余錐の外部積。 -/
def tensorPairCocone : Cocone (pairDiagram W X Y Z) :=
  (colimit.cocone (graphDiagram W X Y)).tensor₂ (colimit.cocone (graphDiagram W Y Z))

/-- 積の各変数の余極限保存から、元の外部積余錐の余極限性を得る。 -/
def tensorPairCocone_isColimit : IsColimit (tensorPairCocone W X Y Z) :=
  IsColimit.tensor₂ (colimit.isColimit (graphDiagram W X Y))
    (colimit.isColimit (graphDiagram W Y Z))

/-- 外部積余錐の成分は、元の二つの標準射の積そのもの。 -/
lemma tensorPairCocone_ι (a b : Word) :
    (tensorPairCocone W X Y Z).ι.app (a, b) =
      (graphInclusion W X Y a ⊗ₘ graphInclusion W Y Z b) := by
  simp only [tensorPairCocone, Cocone.tensor₂, Functor.mapCocone₂,
    Functor.const_obj_obj, curriedTensor_map_app, curriedTensor_obj_map,
    colimit.cocone_x, colimit.cocone_ι, colimitGraph, graphDiagram_obj,
    graphInclusion, tensorHom_def]

/-- 対の図式の余極限と、二つの元の余極限の積との標準同型。 -/
def tensorPairColimitIso :
    colimit (pairDiagram W X Y Z) ≅ colimitGraph W X Y ⊗ colimitGraph W Y Z :=
  (colimit.isColimit (pairDiagram W X Y Z)).coconePointUniqueUpToIso
    (tensorPairCocone_isColimit W X Y Z)

/-- 標準同型は元の全固定語の二つの標準射の積を回収する。 -/
lemma tensorPairColimitIso_fac (a b : Word) :
    colimit.ι (pairDiagram W X Y Z) (a, b) ≫ (tensorPairColimitIso W X Y Z).hom =
      (graphInclusion W X Y a ⊗ₘ graphInclusion W Y Z b) := by
  simpa only [tensorPairColimitIso, colimit.cocone_ι, tensorPairCocone_ι] using
    (colimit.isColimit (pairDiagram W X Y Z)).comp_coconePointUniqueUpToIso_hom
      (tensorPairCocone_isColimit W X Y Z) (a, b)

/-- 二つの実際の余極限の積から、元の合成余錐により定める合成。 -/
def colimitComposition : colimitGraph W X Y ⊗ colimitGraph W Y Z ⟶ colimitGraph W X Z :=
  (tensorPairCocone_isColimit W X Y Z).desc (compositionPairingCocone W X Y Z)

/-- 元の全固定語の対で、元の合成と同じ標準射を厳密に回収する。 -/
lemma colimitComposition_fac (a b : Word) :
    (graphInclusion W X Y a ⊗ₘ graphInclusion W Y Z b) ≫ colimitComposition W X Y Z =
      graphPairing W X Y Z a b := by
  have h := (tensorPairCocone_isColimit W X Y Z).fac (compositionPairingCocone W X Y Z) (a, b)
  simpa only [tensorPairCocone_ι, colimitComposition, compositionPairingCocone] using h

/-- 前工程の対の余極限からの比較は、標準同型と同じ合成の積。 -/
lemma tensorPairColimitIso_comp :
    (tensorPairColimitIso W X Y Z).hom ≫ colimitComposition W X Y Z =
      colimitCompositionPairing W X Y Z :=
  (colimit.isColimit (pairDiagram W X Y Z)).coconePointUniqueUpToIso_hom_desc
    (tensorPairCocone_isColimit W X Y Z)

/-- 全固定語の元の標準射の積上での一致は、元の余極限の積からの射の一致を与える。 -/
lemma tensorPair_hom_ext {K : SSet.{max u v}}
    (f g : colimitGraph W X Y ⊗ colimitGraph W Y Z ⟶ K)
    (h : ∀ a b : Word, (graphInclusion W X Y a ⊗ₘ graphInclusion W Y Z b) ≫ f =
      (graphInclusion W X Y a ⊗ₘ graphInclusion W Y Z b) ≫ g) : f = g := by
  apply (tensorPairCocone_isColimit W X Y Z).hom_ext
  rintro ⟨a, b⟩
  simpa only [tensorPairCocone_ι] using h a b

end SerrePositivity.EInfinity.Hammock
