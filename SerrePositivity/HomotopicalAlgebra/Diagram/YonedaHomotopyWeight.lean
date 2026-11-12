module

public import SerrePositivity.HomotopicalAlgebra.Diagram.YonedaWeights
public import SerrePositivity.HomotopicalAlgebra.Diagram.PointwiseColimitComparison

/-! # A cofibrant homotopy weight from the universal Yoneda diagram

For every cofibrant X, the actual homotopy colimit of the Yoneda copower
diagram is a projectively cofibrant K-opposite diagram weakly augmented
to constant X. The constant diagram need not be projectively cofibrant.
-/

@[expose] public section
universe w v u
noncomputable section
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra

namespace SerrePositivity.DiagramModel.YonedaHomotopyWeight
variable (K : Type w) [SmallCategory K]
  {C : Type u} [Category.{v} C] [ModelCategory C] [IsLocallyPresentable.{w} C]
  (I J : MorphismProperty C) [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{w} I J]

local instance : HasColimitsOfSize.{w, w} C := Smith.locallyPresentable_hasColimits (C := C)
local instance : IsLocallyPresentable.{w} (Kᵒᵖ ⥤ C) :=
  Smith.AccessibleLimits.functorCategory_isLocallyPresentable Kᵒᵖ
abbrev weight (X : C) : Kᵒᵖ ⥤ C := by
  let := Projective.modelCategory Kᵒᵖ I J
  have := Projective.modelCategory_generated Kᵒᵖ I J
  exact (HomotopyColimit.functor K (Projective.generators Kᵒᵖ I)
    (Projective.generators Kᵒᵖ J)).obj (YonedaWeights.family K X)

def augmentation (X : C) : weight K I J X ⟶ (Functor.const Kᵒᵖ).obj X := by
  let := Projective.modelCategory Kᵒᵖ I J
  have := Projective.modelCategory_generated Kᵒᵖ I J
  exact (HomotopyColimit.comparison K (Projective.generators Kᵒᵖ I)
    (Projective.generators Kᵒᵖ J)).app (YonedaWeights.family K X) ≫
      (YonedaWeights.colimitIso K X).hom

lemma evaluation_isCofibrant (X : C) [IsCofibrant X] (l : Kᵒᵖ) :
    let := Projective.modelCategory K I J
    IsCofibrant (YonedaWeights.family K X ⋙ (evaluation Kᵒᵖ C).obj l) := by
  let := Projective.modelCategory K I J
  have := Projective.free_isLeftQuillen K I J l.unop
  have := (evaluationAdjunctionRight C l.unop).isLeftAdjoint
  have : IsCofibrant ((evaluationLeftAdjoint C l.unop).obj X) :=
    Quillen.isCofibrant_obj (evaluationLeftAdjoint C l.unop) X
  exact isCofibrant_of_cofibration (YonedaWeights.evaluationIso K X l).inv

lemma value_isCofibrant (X : C) [IsCofibrant X] (k : K) :
    let := Projective.modelCategory Kᵒᵖ I J
    IsCofibrant ((YonedaWeights.family K X).obj k) := by
  let := Projective.modelCategory Kᵒᵖ I J
  have := Projective.free_isLeftQuillen Kᵒᵖ I J (Opposite.op k)
  have := (evaluationAdjunctionRight C (Opposite.op k)).isLeftAdjoint
  have : IsCofibrant ((evaluationLeftAdjoint C (Opposite.op k)).obj X) :=
    Quillen.isCofibrant_obj (evaluationLeftAdjoint C (Opposite.op k)) X
  exact isCofibrant_of_cofibration (YonedaWeights.freeWeightIso K X k).inv

lemma weight_isCofibrant (X : C) :
    let := Projective.modelCategory Kᵒᵖ I J
    IsCofibrant (weight K I J X) := by
  let := Projective.modelCategory Kᵒᵖ I J
  have := Projective.modelCategory_generated Kᵒᵖ I J
  let := Projective.modelCategory K (Projective.generators Kᵒᵖ I) (Projective.generators Kᵒᵖ J)
  have := HomotopyColimit.replacement_isCofibrant K
    (Projective.generators Kᵒᵖ I) (Projective.generators Kᵒᵖ J) (YonedaWeights.family K X)
  have := Projective.colimit_isLeftQuillen K
    (Projective.generators Kᵒᵖ I) (Projective.generators Kᵒᵖ J)
  exact Quillen.isCofibrant_obj (colim : (K ⥤ Kᵒᵖ ⥤ C) ⥤ _) _

lemma augmentation_weakEquivalence (X : C) [IsCofibrant X] :
    let := Projective.modelCategory Kᵒᵖ I J
    weakEquivalences (Kᵒᵖ ⥤ C) (augmentation K I J X) := by
  let := Projective.modelCategory Kᵒᵖ I J
  have := Projective.modelCategory_generated Kᵒᵖ I J
  have hc := PointwiseColimitComparison.homotopyColimit_comparison_weakEquivalence K Kᵒᵖ I J
    (YonedaWeights.family K X) (evaluation_isCofibrant K I J X)
  exact (weakEquivalences (Kᵒᵖ ⥤ C)).comp_mem _ _ hc
    ((weakEquivalences (Kᵒᵖ ⥤ C)).of_isIso (YonedaWeights.colimitIso K X).hom)

end SerrePositivity.DiagramModel.YonedaHomotopyWeight
