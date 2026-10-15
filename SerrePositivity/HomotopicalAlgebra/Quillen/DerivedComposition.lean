module

public import SerrePositivity.HomotopicalAlgebra.Quillen.Equivalence
public import SerrePositivity.HomotopicalAlgebra.Quillen.CofibrantObjects

/-! # Composition and weak inverse transformations for left Quillen functors

Composition is computed on cofibrant objects. A transformation from a
composite to the identity which is weak on cofibrant objects gives an actual
isomorphism between the composite of derived functors and the identity.
No functorial model factorizations are required.
-/

@[expose] public section
universe vC uC vD uD vE uE vHC uHC vHD uHD vHE uHE
noncomputable section
open CategoryTheory HomotopicalAlgebra

namespace SerrePositivity.Quillen
variable {C : Type uC} [Category.{vC} C]
  {D : Type uD} [Category.{vD} D]
  {E : Type uE} [Category.{vE} E]
  {HC : Type uHC} [Category.{vHC} HC] {HD : Type uHD} [Category.{vHD} HD]
  {HE : Type uHE} [Category.{vHE} HE]
  (QC : C ⥤ HC)
  (QD : D ⥤ HD)
  (QE : E ⥤ HE)
  {F : C ⥤ D}
  {G : D ⥤ E}
  {LF : HC ⥤ HD} {LG : HD ⥤ HE}
  (α : QC ⋙ LF ⟶ F ⋙ QD)
  (β : QD ⋙ LG ⟶ G ⋙ QE)

def leftCompositeComparison : QC ⋙ (LF ⋙ LG) ⟶ (F ⋙ G) ⋙ QE :=
  (Functor.associator QC LF LG).inv ≫ Functor.whiskerRight α LG ≫
    (Functor.associator F QD LG).hom ≫ Functor.whiskerLeft F β ≫
    (Functor.associator F G QE).inv

@[simp] lemma leftCompositeComparison_app (X : C) :
    (leftCompositeComparison QC QD QE α β).app X =
      LG.map (α.app X) ≫ β.app (F.obj X) := by
  simp [leftCompositeComparison]

variable [ModelCategory C] [ModelCategory D] [ModelCategory E]
  [QC.IsLocalization (weakEquivalences C)] [QD.IsLocalization (weakEquivalences D)]
  [QE.IsLocalization (weakEquivalences E)] [F.IsLeftAdjoint] [IsLeftQuillen F] [IsLeftQuillen G]
  [LF.IsLeftDerivedFunctor α (weakEquivalences C)]
  [LG.IsLeftDerivedFunctor β (weakEquivalences D)]

lemma leftCompositeComparison_isIso (X : C) [IsCofibrant X] :
    IsIso ((leftCompositeComparison QC QD QE α β).app X) := by
  have := leftComparison_isIso QC QD α X
  have := isCofibrant_obj F X
  have := leftComparison_isIso QD QE β (F.obj X)
  rw [leftCompositeComparison_app]
  infer_instance

lemma leftDerived_comp : (LF ⋙ LG).IsLeftDerivedFunctor
    (leftCompositeComparison QC QD QE α β) (weakEquivalences C) := by
  apply (cofibrant_derives QE (F ⋙ G)).isLeftDerivedFunctor_of_isIso
  intro X
  exact leftCompositeComparison_isIso QC QD QE α β X.obj

end SerrePositivity.Quillen
