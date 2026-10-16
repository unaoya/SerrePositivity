module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedCoherentTriangles
public import SerrePositivity.HomotopicalAlgebra.Simplicial.NerveSmallFamilies
public import SerrePositivity.HomotopicalAlgebra.Simplicial.UniverseLiftProductParameter

/-! # Entire mixed triangle families in the original Hom universe on every external chain -/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.MonoidalCategory HomotopicalAlgebra
open SerrePositivity.SimplicialModel SerrePositivity.HomotopyFunctionComplex
open ResolutionMixedDiagram NerveBiparameterMaps

namespace SerrePositivity.HomotopyFunctionComplex.ResolutionMixedSmallFamilies
variable (C : Type u) [Category.{v} C] [ModelCategory C] [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)

abbrev tuples := cornerA C ⋙ ResolutionArrowTuples.tuples C
abbrev smallParameter := NerveCylinderBoundary.product (tuples C)
  (SSet.stdSimplex.{v}.obj (SimplexCategory.mk 2))
abbrev parameterIso : NerveMovingParameter.lifted.{u} (smallParameter C) ≅
    ResolutionMixedBoundary.fullParameter C := UniverseLiftProductParameter.iso (tuples C) 2

/-- Change coordinates on the same whole coherent triangle system. -/
def system (side : Bool) : NerveMovingParameter.System.{u, v}
    (NerveMovingParameter.lifted.{u} (smallParameter C)) (smallValues C) :=
  restrict _ _ _ (parameterIso C).hom (ResolutionMixedCoherentTriangles.coherent C hcof hfib side)

/-- Every external chain carries an entire small tuple-and-triangle family. -/
def family (side : Bool) {n : ℕ} (c : ComposableArrows (Index C) n) :
    (smallParameter C).obj (c.obj 0) ⊗ SSet.stdSimplex.{v}.obj (SimplexCategory.mk n) ⟶
      (smallValues C).obj (c.obj (Fin.last n)) :=
  NerveSmallFamilies.family (smallParameter C) (smallValues C) (system C hcof hfib side) c

lemma family_naturality (side : Bool) {n m : ℕ} (c : ComposableArrows (Index C) n)
    (θ : SimplexCategory.mk m ⟶ SimplexCategory.mk n) :
    (smallParameter C).obj (c.obj 0) ◁ SSet.stdSimplex.map θ ≫ family C hcof hfib side c =
      (((smallParameter C).map (c.map (homOfLE (Fin.zero_le (θ.toOrderHom 0))))) ▷
        SSet.stdSimplex.obj (SimplexCategory.mk m) ≫
        family C hcof hfib side ((SimplexCategory.toCat.map θ).toFunctor ⋙ c)) ≫
      (smallValues C).map (c.map (homOfLE (Fin.le_last (θ.toOrderHom (Fin.last m))))) :=
  NerveSmallFamilies.family_naturality _ _ _ c θ

lemma point_recover (side : Bool) (p : Index C) :
    NerveSmallFamilies.point (smallParameter C) (smallValues C) (system C hcof hfib side) p =
    RelativeChoiceSpace.family (ResolutionMixedTriangles.oldInclusion C p)
      (ResolutionMixedTriangles.oldBoundary C p)
      (ResolutionMixedTriangles.oldTriangle C hcof hfib p side) := by
  apply (congrArg UniverseLift.lower
    ((evaluate_restrict (ResolutionMixedBoundary.fullParameter C) (smallValues C)
      (ResolutionMixedCoherentTriangles.coherent C hcof hfib side)
      (NerveMovingParameter.lifted.{u} (smallParameter C)) (parameterIso C).hom p).trans
      (congrArg (fun k => (parameterIso C).hom.app p ≫ k)
        (ResolutionMixedCoherentTriangles.coherent_evaluate C hcof hfib side p)))).trans
  change UniverseLift.lower ((UniverseLiftProductParameter.iso (tuples C) 2).hom.app p ≫
    UniverseLift.simplexTensorMap _) = _
  rw [UniverseLiftProductParameter.hom_family, UniverseLift.lower_map]
  rfl

abbrev smallIntervalParameter := NerveCylinderBoundary.product (tuples C)
  (SSet.stdSimplex.{v}.obj (SimplexCategory.mk 1))
abbrev smallFaceMap (k : Fin 3) : smallIntervalParameter C ⟶ smallParameter C :=
  NerveCylinderBoundary.vertical (SSet.stdSimplex.δ k) (tuples C)
abbrev intervalParameterIso : NerveMovingParameter.lifted.{u} (smallIntervalParameter C) ≅
    ResolutionMixedIntervalRestrictions.intervalParameters C :=
  UniverseLiftProductParameter.iso (tuples C) 1

def faceSystem (side : Bool) (k : Fin 3) : NerveMovingParameter.System.{u, v}
    (NerveMovingParameter.lifted.{u} (smallIntervalParameter C)) (smallValues C) :=
  restrict _ _ _ (intervalParameterIso C).hom (ResolutionMixedFaceSystems.faces C hcof hfib side k)

lemma system_face (side : Bool) (k : Fin 3) : system C hcof hfib side ≫ restriction _ _
    (NerveMovingParameter.lifted (smallValues C))
    (Functor.whiskerRight (smallFaceMap C k) SSet.uliftFunctor.{u, v}) =
    faceSystem C hcof hfib side k := by
  have hc : Functor.whiskerRight (smallFaceMap C k) SSet.uliftFunctor.{u, v} ≫
      (parameterIso C).hom = (intervalParameterIso C).hom ≫
      NerveCylinderBoundary.vertical (SSet.stdSimplex.δ k) (parameters C) :=
    UniverseLiftProductParameter.operator (tuples C) (SimplexCategory.δ k)
  change (ResolutionMixedCoherentTriangles.coherent C hcof hfib side ≫
    restriction _ _ _ (parameterIso C).hom) ≫ _ = _
  rw [Category.assoc, restriction_comp, hc, ← restriction_comp, ← Category.assoc,
    ResolutionMixedCoherentTriangles.coherent_face]
  rfl

abbrev faceFamily (side : Bool) (k : Fin 3) {n : ℕ} (c : ComposableArrows (Index C) n) :=
  NerveSmallFamilies.family (smallIntervalParameter C) (smallValues C)
    (faceSystem C hcof hfib side k) c

lemma family_face (side : Bool) (k : Fin 3) {n : ℕ} (c : ComposableArrows (Index C) n) :
    faceFamily C hcof hfib side k c =
    ((smallFaceMap C k).app (c.obj 0) ▷ SSet.stdSimplex.obj (SimplexCategory.mk n)) ≫
      family C hcof hfib side c :=
  (congrArg (fun a => NerveSmallFamilies.family (smallIntervalParameter C) (smallValues C) a c)
    (system_face C hcof hfib side k).symm).trans
    (NerveSmallFamilies.family_restrict _ _ _ _ _ c)

lemma shared_diagonal {n : ℕ} (c : ComposableArrows (Index C) n) :
    faceFamily C hcof hfib true 1 c = faceFamily C hcof hfib false 1 c := by
  apply congrArg (fun a => NerveSmallFamilies.family (smallIntervalParameter C) (smallValues C) a c)
  exact congrArg (restrict _ _ _ (intervalParameterIso C).hom)
    (ResolutionMixedFaceSystems.shared_diagonal C hcof hfib)

end SerrePositivity.HomotopyFunctionComplex.ResolutionMixedSmallFamilies
