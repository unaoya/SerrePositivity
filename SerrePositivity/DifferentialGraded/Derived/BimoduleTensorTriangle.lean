module
public import SerrePositivity.DifferentialGraded.Derived.BimoduleTensorEvaluation
public import SerrePositivity.DifferentialGraded.Tensor.Triangle

/-! # 固定した右相対K-flat因子に関する導来合成の三角coherence -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory CategoryTheory.Functor
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w) (E : Type z)
  [DGCategory A B] [DGCategory A C] [DGCategory A E] [Small.{u} B] [Small.{u} C]

lemma derivedTriangle (Q : BimoduleCategory A C E)
    (hQ : Bimodule.rightRelativeKFlat A C E (BimoduleCategory.underlying A C E Q)) :
    (derivedAssociatorIso A B C C E
        (BimoduleCategory.of A C C (Bimodule.diagonal A C)) Q
        (Bimodule.diagonal_rightRelativeKFlat A C) hQ).hom ≫
      derivedComposeWithMap A B C E
        (Bimodule.rightRelativeKFlat_compose A C C E (Bimodule.diagonal A C)
          (BimoduleCategory.underlying A C E Q) (Bimodule.diagonal_rightRelativeKFlat A C) hQ)
        hQ (leftBimoduleUnitIso A C E (BimoduleCategory.underlying A C E Q)).hom =
    whiskerRight (derivedRightUnitIso A B C).hom (derivedComposeWith A B C E Q hQ) ≫
      (Functor.leftUnitor (derivedComposeWith A B C E Q hQ)).hom := by
  apply bimoduleDerivedNatTrans_ext A B C
  intro P
  simp only [NatTrans.comp_app, whiskerRight_app, Functor.leftUnitor_hom_app,
    derivedAssociatorIso_base_app, derivedComposeWithMap_base_app,
    derivedRightUnitIso_base_app, derivedComposeWith_map_base]
  rw [← CategoryTheory.Functor.map_comp]
  exact congrArg (fun f => (bimoduleToDerived A B E).map f)
    (triangle A B C E (BimoduleCategory.underlying A B C P)
      (BimoduleCategory.underlying A C E Q)).symm

end SerrePositivity.DifferentialGraded.BimoduleTensor
