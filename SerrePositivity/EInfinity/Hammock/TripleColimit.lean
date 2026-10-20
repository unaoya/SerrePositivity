module

public import SerrePositivity.EInfinity.Hammock.ColimitComposition

/-!
# 三つの元の hammock 余極限の積の一意性

概要：三つの元の余極限の積からの射は、全固定語の標準射の積で決まる。
方針：元の外部積余錐と第三の余錐に IsColimit.tensor₂ を反復する。
規約：添字圏の filtered 性や同じ添字での積保存は使わない。
使われ方：元の余極限上の合成の結合則の降下。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.EInfinity.Hammock
open CategoryTheory CategoryTheory.Limits MonoidalCategory

variable {C : Type u} [Category.{v} C] (W : MorphismProperty C) [W.IsMultiplicative]
  (X Y Z V : C)

lemma tensorTriple_hom_ext {K : SSet.{max u v}}
    (f g : (colimitGraph W X Y ⊗ colimitGraph W Y Z) ⊗ colimitGraph W Z V ⟶ K)
    (h : ∀ a b c : Word,
      ((graphInclusion W X Y a ⊗ₘ graphInclusion W Y Z b) ⊗ₘ graphInclusion W Z V c) ≫ f =
      ((graphInclusion W X Y a ⊗ₘ graphInclusion W Y Z b) ⊗ₘ graphInclusion W Z V c) ≫ g) :
    f = g := by
  apply (IsColimit.tensor₂ (tensorPairCocone_isColimit W X Y Z)
    (colimit.isColimit (graphDiagram W Z V))).hom_ext
  rintro ⟨⟨a, b⟩, c⟩
  simpa only [Cocone.tensor₂, Functor.mapCocone₂, Functor.const_obj_obj,
    curriedTensor_map_app, curriedTensor_obj_map, curriedTensor_obj_obj,
    colimit.cocone_x, colimit.cocone_ι,
    tensorPairCocone_ι, tensorPairCocone, colimitGraph, graphDiagram_obj,
    graphInclusion, tensorHom_def, Category.assoc] using h a b c

end SerrePositivity.EInfinity.Hammock
