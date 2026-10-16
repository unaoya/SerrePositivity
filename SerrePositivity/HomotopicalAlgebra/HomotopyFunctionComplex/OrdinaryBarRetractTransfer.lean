module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarRetractSystem

/-! # Transfer of actual ambient arrows with constant unit comparison intervals

The binary comparison is defined on arbitrary actual arrows, including the
identity arrows used for coherent units. Its interval is literally constant
when either input is an identity. This does not impose laws on chosen actions.
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open SerrePositivity.SimplicialModel

namespace SerrePositivity.HomotopyFunctionComplex.OrdinaryBarRetractSystem
variable {C : Type u} [Category.{v} C] [HomotopicalAlgebra.ModelCategory C]
  [HomotopicalAlgebra.ModelCategory SSet.{v}]
  (hcof : HomotopicalAlgebra.cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : HomotopicalAlgebra.fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)

def transferArrow {b c : Cᵒᵖ × C} (a : ambient hcof hfib b ⟶ ambient hcof hfib c) :
    lifted hcof hfib b ⟶ lifted hcof hfib c :=
  section_ hcof hfib b ≫ a ≫ projection hcof hfib c

lemma transferArrow_id (b : Cᵒᵖ × C) : transferArrow hcof hfib (𝟙 (ambient hcof hfib b)) =
    𝟙 (lifted hcof hfib b) := by
  simpa only [transferArrow, Category.id_comp] using section_fac hcof hfib b

def transferCompositionHomotopy {b c d : Cᵒᵖ × C}
    (a : ambient hcof hfib b ⟶ ambient hcof hfib c)
    (e : ambient hcof hfib c ⟶ ambient hcof hfib d) :
    SSet.Homotopy (transferArrow hcof hfib (a ≫ e))
      (transferArrow hcof hfib a ≫ transferArrow hcof hfib e) := by
  have H := HomotopyClasses.postHomotopy (e ≫ projection hcof hfib d)
    (HomotopyClasses.preHomotopy (section_ hcof hfib b ≫ a) (contraction hcof hfib c))
  simpa only [transferArrow, Category.assoc, Category.id_comp, Category.comp_id] using H

lemma transferCompositionHomotopy_h {b c d : Cᵒᵖ × C}
    (a : ambient hcof hfib b ⟶ ambient hcof hfib c)
    (e : ambient hcof hfib c ⟶ ambient hcof hfib d) :
    (transferCompositionHomotopy hcof hfib a e).h =
      (section_ hcof hfib b ≫ a) ▷ SSet.stdSimplex.obj (SimplexCategory.mk 1) ≫
        (contraction hcof hfib c).h ≫ e ≫ projection hcof hfib d := rfl

lemma transferCompositionHomotopy_left_id {b c : Cᵒᵖ × C}
    (a : ambient hcof hfib b ⟶ ambient hcof hfib c) :
    (transferCompositionHomotopy hcof hfib (𝟙 _) a).h =
      fst (lifted hcof hfib b) (SSet.stdSimplex.obj (SimplexCategory.mk 1)) ≫
        transferArrow hcof hfib a := by
  rw [transferCompositionHomotopy_h, Category.comp_id, ← Category.assoc,
    ← Category.assoc, contraction_on_section]
  simp only [transferArrow, Category.assoc]

lemma transferCompositionHomotopy_right_id {b c : Cᵒᵖ × C}
    (a : ambient hcof hfib b ⟶ ambient hcof hfib c) :
    (transferCompositionHomotopy hcof hfib a (𝟙 _)).h =
      fst (lifted hcof hfib b) (SSet.stdSimplex.obj (SimplexCategory.mk 1)) ≫
        transferArrow hcof hfib a := by
  rw [transferCompositionHomotopy_h, Category.id_comp, contraction_over,
    whiskerRight_fst_assoc]
  simp only [transferArrow, Category.assoc]

def smallTransferArrow {b c : Cᵒᵖ × C}
    (a : ambient hcof hfib b ⟶ ambient hcof hfib c) : small hcof hfib b ⟶ small hcof hfib c :=
  UniverseLift.lower (transferArrow hcof hfib a)

lemma smallTransferArrow_id (b : Cᵒᵖ × C) :
    smallTransferArrow hcof hfib (𝟙 (ambient hcof hfib b)) = 𝟙 (small hcof hfib b) := by
  rw [smallTransferArrow, transferArrow_id]
  rfl

def smallTransferCompositionHomotopy {b c d : Cᵒᵖ × C}
    (a : ambient hcof hfib b ⟶ ambient hcof hfib c)
    (e : ambient hcof hfib c ⟶ ambient hcof hfib d) :
    SSet.Homotopy (smallTransferArrow hcof hfib (a ≫ e))
      (smallTransferArrow hcof hfib a ≫ smallTransferArrow hcof hfib e) :=
  UniverseLift.lowerHomotopy.{max u v, v} (transferCompositionHomotopy hcof hfib a e)

lemma smallTransferCompositionHomotopy_left_id {b c : Cᵒᵖ × C}
    (a : ambient hcof hfib b ⟶ ambient hcof hfib c) :
    (smallTransferCompositionHomotopy hcof hfib (𝟙 _) a).h =
      fst (small hcof hfib b) (SSet.stdSimplex.obj (SimplexCategory.mk 1)) ≫
        smallTransferArrow hcof hfib a := by
  change UniverseLift.lowerSimplexTensor
    (transferCompositionHomotopy hcof hfib (𝟙 _) a).h = _
  rw [transferCompositionHomotopy_left_id]
  change UniverseLift.lowerSimplexTensor
    (fst _ _ ≫ UniverseLift.map (smallTransferArrow hcof hfib a)) = _
  rw [← UniverseLift.simplexTensorMap_constant,
    UniverseLift.lowerSimplexTensor_simplexTensorMap]

lemma smallTransferCompositionHomotopy_right_id {b c : Cᵒᵖ × C}
    (a : ambient hcof hfib b ⟶ ambient hcof hfib c) :
    (smallTransferCompositionHomotopy hcof hfib a (𝟙 _)).h =
      fst (small hcof hfib b) (SSet.stdSimplex.obj (SimplexCategory.mk 1)) ≫
        smallTransferArrow hcof hfib a := by
  change UniverseLift.lowerSimplexTensor
    (transferCompositionHomotopy hcof hfib a (𝟙 _)).h = _
  rw [transferCompositionHomotopy_right_id]
  change UniverseLift.lowerSimplexTensor
    (fst _ _ ≫ UniverseLift.map (smallTransferArrow hcof hfib a)) = _
  rw [← UniverseLift.simplexTensorMap_constant,
    UniverseLift.lowerSimplexTensor_simplexTensorMap]

end SerrePositivity.HomotopyFunctionComplex.OrdinaryBarRetractSystem
