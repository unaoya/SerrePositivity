module

public import SerrePositivity.HomotopicalAlgebra.Diagram.ColimitFrame
public import SerrePositivity.HomotopicalAlgebra.Diagram.ConstantWeightHom

/-! # The degree-zero frame colimit compares weakly to the actual hocolim

Both degree zero of the specified projective cosimplicial resolution and
its augmentation target Q_K(D) are projectively cofibrant. The augmentation
is a weak equivalence. The actual left Quillen colimit therefore sends it
to a weak equivalence, naturally in the original diagram D.
-/

@[expose] public section
universe w v u
noncomputable section
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SerrePositivity.Reedy SerrePositivity.HomotopyFunctionComplex

namespace SerrePositivity.DiagramModel.DegreeZeroHomotopyColimit
variable (K : Type w) [SmallCategory K] {C : Type u} [Category.{v} C]
  [ModelCategory C] [IsLocallyPresentable.{w} C]
  (I J : MorphismProperty C) [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{w} I J]

local instance : HasColimitsOfSize.{w, w} C := Smith.locallyPresentable_hasColimits (C := C)

abbrev family : (K ⥤ C) ⥤ (K ⥤ C) := ColimitFrame.diagramResolution K I J ⋙
  (CategoryTheory.evaluation SimplexCategory (K ⥤ C)).obj (SimplexCategory.mk 0)

def augmentation : family K I J ⟶ HomotopyColimit.replacement K I J := by
  let := Projective.modelCategory K I J
  exact Functor.whiskerRight
    (Functor.whiskerLeft (HomotopyColimit.replacement K I J)
      (ColimitFrame.resolutionFamily K I J).augmentation)
    ((CategoryTheory.evaluation SimplexCategory (K ⥤ C)).obj (SimplexCategory.mk 0))

abbrev colimitFamily : (K ⥤ C) ⥤ C := family K I J ⋙ colim

abbrev comparison : colimitFamily K I J ⟶ HomotopyColimit.functor K I J :=
  Functor.whiskerRight (augmentation K I J) colim

lemma isCofibrant (D : K ⥤ C) :
    let := Projective.modelCategory K I J
    IsCofibrant ((family K I J).obj D) := by
  let := Projective.modelCategory K I J
  exact cosimplicialFrame_isCofibrant_obj ((ColimitFrame.diagramResolution K I J).obj D)
    ((ColimitFrame.resolutionFamily K I J).cofibrant
      ((HomotopyColimit.replacement K I J).obj D)) (SimplexCategory.mk 0)

lemma augmentation_weakEquivalence (D : K ⥤ C) :
    let := Projective.modelCategory K I J
    weakEquivalences (K ⥤ C) ((augmentation K I J).app D) := by
  let := Projective.modelCategory K I J
  exact ((ColimitFrame.resolutionFamily K I J).atObject
    ((HomotopyColimit.replacement K I J).obj D)).augmentation_weakEquivalence (SimplexCategory.mk 0)

lemma comparison_weakEquivalence (D : K ⥤ C) :
    weakEquivalences C ((comparison K I J).app D) := by
  let := Projective.modelCategory K I J
  have := Projective.colimit_isLeftQuillen K I J
  have : IsCofibrant ((family K I J).obj D) := isCofibrant K I J D
  have := HomotopyColimit.replacement_isCofibrant K I J D
  have : WeakEquivalence ((augmentation K I J).app D) :=
    ⟨augmentation_weakEquivalence K I J D⟩
  exact (weakEquivalence_iff _).mp
    (Quillen.map_weakEquivalence_of_cofibrant (colim : (K ⥤ C) ⥤ C) ((augmentation K I J).app D))

end SerrePositivity.DiagramModel.DegreeZeroHomotopyColimit
