module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.UniverseLiftTensor
public import SerrePositivity.HomotopicalAlgebra.Simplicial.NerveProductParameter

/-! # The actual small-universe model of a moving parameter times a standard simplex -/

@[expose] public section
universe w v uD vD
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.MonoidalCategory
open SerrePositivity.SimplicialModel

namespace SerrePositivity.SimplicialModel.UniverseLiftProductParameter
variable {D : Type uD} [Category.{vD} D] (K : D ⥤ SSet.{v}) (m : ℕ)

/-- A natural isomorphism of actual parameter diagrams, without any model structure. -/
def iso : NerveMovingParameter.lifted.{w} (NerveCylinderBoundary.product K
    (SSet.stdSimplex.{v}.obj (SimplexCategory.mk m))) ≅
    NerveCylinderBoundary.product (NerveMovingParameter.lifted.{w} K)
      (SSet.stdSimplex.{max w v}.obj (SimplexCategory.mk m)) :=
  NatIso.ofComponents (fun d => UniverseLift.tensorIso (K.obj d)
    (SSet.stdSimplex.obj (SimplexCategory.mk m)) ≪≫
      whiskerLeftIso (UniverseLift.obj.{w} (K.obj d)) (UniverseLift.stdIso m))
    (by intro d e f; ext n x; rfl)

lemma hom_family (d : D) {P : SSet.{v}}
    (h : K.obj d ⊗ SSet.stdSimplex.{v}.obj (SimplexCategory.mk m) ⟶ P) :
    ((iso.{w} K m).hom.app d) ≫ UniverseLift.simplexTensorMap h = UniverseLift.map h := by
  ext n x
  rfl

lemma operator {m n : ℕ} (θ : SimplexCategory.mk m ⟶ SimplexCategory.mk n) :
    Functor.whiskerRight (NerveCylinderBoundary.vertical (SSet.stdSimplex.map θ) K)
      SSet.uliftFunctor.{w, v} ≫ (iso.{w} K n).hom =
    (iso.{w} K m).hom ≫ NerveCylinderBoundary.vertical (SSet.stdSimplex.map θ)
      (NerveMovingParameter.lifted.{w} K) := by
  ext d s x
  rfl

end SerrePositivity.SimplicialModel.UniverseLiftProductParameter
