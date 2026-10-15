module
public import SerrePositivity.DifferentialGraded.Complexes.ConeRotation
public import SerrePositivity.DifferentialGraded.Module.ConeRotationInputs
public import SerrePositivity.DifferentialGraded.Module.ConeContractible
public import SerrePositivity.DifferentialGraded.Module.ConeHomotopyDesc

/-! # coneの回転比較射と各評価での既存比較との一致 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

@[simp] lemma moduleConeRotationHom_eval {M N : ModuleCategory A D} (f : M ⟶ N) (x : D) :
    (moduleEvaluation A D x).map (moduleConeRotationHom A D f) =
      complexConeRotationHom ((moduleEvaluation A D x).map f)
        ((moduleEvaluation A D x).map (moduleConeInr A D f)) (moduleConeInr_eval A D f x) := by
  unfold moduleConeRotationHom
  rw [moduleConeLiftOfCycle_eval]
  apply Cochain.ofHom_injective
  rw [mappingCone.ofHom_lift, complexConeRotationHom_cochain]
  change mappingCone.liftCochain ((moduleEvaluation A D x).map (moduleConeInr A D f))
    ((moduleHomπ A D (ForgetEnrichment.to (Complex A) (moduleShiftObj A D 1 M))
      (ForgetEnrichment.to (Complex A) N) x).f 1 (moduleConeRotationFirst A D f))
    ((moduleHomπ A D (ForgetEnrichment.to (Complex A) (moduleShiftObj A D 1 M))
      (ForgetEnrichment.to (Complex A) (moduleCone A D f)) x).f 0
        (moduleConeRotationSecond A D f)) (zero_add 1) = _
  rw [moduleConeRotationFirst_π, moduleConeRotationSecond_π]

@[reassoc] lemma moduleConeInr_connecting_zero {M N : ModuleCategory A D} (f : M ⟶ N) :
    moduleConeInr A D f ≫ moduleConeConnecting A D f = 0 := by
  apply moduleMorphism_ext
  intro x
  rw [CategoryTheory.Functor.map_comp, moduleConeInr_eval, moduleConeConnecting_eval,
    CategoryTheory.Functor.map_zero]
  exact mappingCone.inr_triangleδ _

lemma moduleConeRotationInv_condition {M N : ModuleCategory A D} (f : M ⟶ N) :
    (moduleHom A D (ForgetEnrichment.to (Complex A) N)
      (ForgetEnrichment.to (Complex A) (moduleShiftObj A D 1 M))).d (-1) 0 0 =
      (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A)
        (moduleConeInr A D f ≫ moduleConeConnecting A D f))).val := by
  rw [map_zero, moduleConeInr_connecting_zero, moduleHomCycle_zero]

def moduleConeRotationInv {M N : ModuleCategory A D} (f : M ⟶ N) :
    moduleCone A D (moduleConeInr A D f) ⟶ moduleShiftObj A D 1 M :=
  moduleConeDescOfBoundary A D (moduleConeInr A D f) 0
    (moduleConeConnecting A D f) (moduleConeRotationInv_condition A D f)

@[simp] lemma moduleConeRotationInv_eval {M N : ModuleCategory A D} (f : M ⟶ N) (x : D) :
    (moduleEvaluation A D x).map (moduleConeRotationInv A D f) =
      complexConeRotationInv ((moduleEvaluation A D x).map f)
        ((moduleEvaluation A D x).map (moduleConeInr A D f)) (moduleConeInr_eval A D f x) := by
  unfold moduleConeRotationInv
  rw [moduleConeDescOfBoundary_eval]
  apply Cochain.ofHom_injective
  rw [mappingCone.ofHom_desc, complexConeRotationInv_cochain, map_zero,
    moduleConeConnecting_eval]

lemma moduleConeRotation_hom_inv {M N : ModuleCategory A D} (f : M ⟶ N) :
    moduleConeRotationHom A D f ≫ moduleConeRotationInv A D f = 𝟙 _ := by
  apply moduleMorphism_ext
  intro x
  rw [CategoryTheory.Functor.map_comp, moduleConeRotationHom_eval,
    moduleConeRotationInv_eval, CategoryTheory.Functor.map_id]
  exact complexConeRotation_hom_inv _ _ _

end SerrePositivity.DifferentialGraded
