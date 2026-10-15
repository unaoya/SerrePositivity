module

public import SerrePositivity.HomotopicalAlgebra.Enriched.UnitAxiom
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.EnrichedTensorFrameHom
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FramePreservation
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.CosimplicialFrameFamily
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.ChosenMapComparison

/-! # Actual ordinary source frames from a resolved enriching unit

Resolve a cofibrant unit replacement in V, tensor it with the specified
QX, and augment through the represented unit map and QX → X. The action
unit axiom supplies the degreewise weak equivalences. This permits a
noncofibrant enriching unit.
-/

@[expose] public section
universe vV uV vC uC
noncomputable section
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open CategoryTheory.MonoidalCategory
open SerrePositivity.HomotopyFunctionComplex SerrePositivity.Reedy

namespace SerrePositivity.Enriched.UnitFrame
variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  {C : Type uC} [Category.{vC} C] [EnrichedOrdinaryCategory V C]
  (P : TensorCotensor V C)

/-- The ordinary augmentation induced by an actual augmentation to the enriching unit. -/
def augmentationBase (A : SimplexCategory ⥤ V)
    (a : A ⟶ (Functor.const SimplexCategory).obj (𝟙_ V)) :
    EnrichedTensorFrame.family P A ⟶ Functor.const SimplexCategory where
  app X :=
    { app n := (P.tensor.map (a.app n)).app X ≫ P.unitMap X
      naturality n m f := by
        change (P.tensor.map (A.map f)).app X ≫
          ((P.tensor.map (a.app m)).app X ≫ P.unitMap X) =
          ((P.tensor.map (a.app n)).app X ≫ P.unitMap X) ≫ 𝟙 X
        have ha : A.map f ≫ a.app m = a.app n :=
          (a.naturality f).trans (Category.comp_id _)
        rw [Category.comp_id, ← Category.assoc, ← NatTrans.comp_app, ← P.tensor.map_comp, ha] }
  naturality X Z f := by
    ext n
    change (P.tensor.obj (A.obj n)).map f ≫
      ((P.tensor.map (a.app n)).app Z ≫ P.unitMap Z) =
      ((P.tensor.map (a.app n)).app X ≫ P.unitMap X) ≫ f
    rw [← Category.assoc, (P.tensor.map (a.app n)).naturality f, Category.assoc]
    change (P.tensor.map (a.app n)).app X ≫ ((P.tensor.obj (𝟙_ V)).map f ≫ P.unitMap Z) = _
    rw [P.unitMap_naturality f, ← Category.assoc]

variable [ModelCategory V] [ModelCategory C]
  (cofV : MorphismProperty.FunctorialFactorizationData (cofibrations V) (trivialFibrations V))
  (cofC : MorphismProperty.FunctorialFactorizationData (cofibrations C) (trivialFibrations C))
  (U : V) (q : U ⟶ 𝟙_ V)

abbrev diagram : SimplexCategory ⥤ V := (cosimplicialResolutionFamily cofV).obj.obj U

abbrev unitAugmentation : diagram cofV U ⟶ (Functor.const SimplexCategory).obj (𝟙_ V) :=
  (cosimplicialResolutionFamily cofV).augmentation.app U ≫ (Functor.const SimplexCategory).map q

abbrev family : C ⥤ (SimplexCategory ⥤ C) :=
  cofibrantSource cofC ⋙ EnrichedTensorFrame.family P (diagram cofV U)

def augmentation : family P cofV cofC U ⟶ Functor.const SimplexCategory :=
  Functor.whiskerLeft (cofibrantSource cofC)
      (augmentationBase P (diagram cofV U) (unitAugmentation cofV U q)) ≫
    Functor.whiskerRight (cofibrantSourceComparison cofC) (Functor.const SimplexCategory)


variable [Quillen.IsQuillenBifunctor P.tensor]

lemma cofibrant (X : C) :
    reedyLeft simplex (cofibrations C) (initial.to ((family P cofV cofC U).obj X)) := by
  let QX := (cofibrantSource cofC).obj X
  have : IsCofibrant QX := cofibrantSource_isCofibrant cofC X
  have : (P.tensor.flip.obj QX).IsLeftAdjoint := (P.tensorHom.adj QX).isLeftAdjoint
  have := tensor_parameter_isLeftQuillen P QX
  exact leftQuillen_frame_reedyCofibrant (P.tensor.flip.obj QX) (diagram cofV U)
    ((cosimplicialResolutionFamily cofV).cofibrant U)

variable (hU : TensorUnitReplacementAxiom P U q)

include hU in
lemma weak (X : C) (n : SimplexCategory) :
    weakEquivalences C (((augmentation P cofV cofC U q).app X).app n) := by
  let QX := (cofibrantSource cofC).obj X
  let a := (cosimplicialResolutionFamily cofV).augmentation.app U
  have : IsCofibrant QX := cofibrantSource_isCofibrant cofC X
  have : IsCofibrant U := hU.cofibrant
  have : IsCofibrant (((Functor.const SimplexCategory).obj U).obj n) :=
    inferInstanceAs (IsCofibrant U)
  have : IsCofibrant ((diagram cofV U).obj n) :=
    cosimplicialFrame_isCofibrant_obj (diagram cofV U)
      ((cosimplicialResolutionFamily cofV).cofibrant U) n
  have := tensor_parameter_isLeftQuillen P QX
  have : WeakEquivalence (a.app n) :=
    ⟨((cosimplicialResolutionFamily cofV).atObject U).augmentation_weakEquivalence n⟩
  have ht : weakEquivalences C ((P.tensor.map (a.app n)).app QX) :=
    (weakEquivalence_iff _).mp (Quillen.map_weakEquivalence_of_cofibrant
      (P.tensor.flip.obj QX) (a.app n))
  have hu := hU.tensor QX inferInstance
  have hq := (cofibrantSourceComparison_trivialFibration cofC X).2
  have he : ((augmentation P cofV cofC U q).app X).app n =
      ((P.tensor.map (a.app n)).app QX ≫ ((P.tensor.map q).app QX ≫ P.unitMap QX)) ≫
        (cofibrantSourceComparison cofC).app X := by
    change ((P.tensor.map (a.app n ≫ q)).app QX ≫ P.unitMap QX) ≫
      (cofibrantSourceComparison cofC).app X = _
    rw [P.tensor.map_comp, NatTrans.comp_app]
    simp only [Category.assoc]
  rw [he]
  exact (weakEquivalences C).comp_mem _ _ ((weakEquivalences C).comp_mem _ _ ht hu) hq

/-- A fully constructed ordinary source frame family, with a genuinely weak augmentation. -/
def asFrame : CosimplicialFrameFamily (C := C) where
  obj := family P cofV cofC U
  augmentation := augmentation P cofV cofC U q
  cofibrant := cofibrant P cofV cofC U
  weak := weak P cofV cofC U q hU

end SerrePositivity.Enriched.UnitFrame
