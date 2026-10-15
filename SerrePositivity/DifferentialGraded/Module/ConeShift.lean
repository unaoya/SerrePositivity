module
public import SerrePositivity.DifferentialGraded.Module.ConeShiftElements

/-! # 加群圏でのconeと整数shiftの同型 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

def moduleConeShiftHom (s : ℤ) {M N : ModuleCategory A D} (f : M ⟶ N) :
    moduleShiftObj A D s (moduleCone A D f) ⟶ moduleCone A D (moduleShiftMap A D s f) :=
  moduleConeLiftOfCycle A D (moduleShiftMap A D s f)
    (moduleConeShiftFirst A D s f) (moduleConeShiftSecond A D s f)
    (moduleConeShiftFirst_closed A D s f) (moduleConeShiftInputs_cycle A D s f)

def moduleConeShiftInv (s : ℤ) {M N : ModuleCategory A D} (f : M ⟶ N) :
    moduleCone A D (moduleShiftMap A D s f) ⟶ moduleShiftObj A D s (moduleCone A D f) :=
  moduleConeDescOfBoundary A D (moduleShiftMap A D s f) (moduleConeShiftLeftInput A D s f)
    (moduleShiftMap A D s (moduleConeInr A D f)) (moduleConeShiftLeftInput_d A D s f)

@[simp] lemma moduleConeShiftHom_eval (s : ℤ) {M N : ModuleCategory A D} (f : M ⟶ N) (x : D) :
    (moduleEvaluation A D x).map (moduleConeShiftHom A D s f) =
      (complexConeShiftIso ((moduleEvaluation A D x).map f) s
        ((moduleEvaluation A D x).map (moduleShiftMap A D s f))
        (moduleShiftMap_eval A D s f x)).hom := by
  unfold moduleConeShiftHom
  rw [moduleConeLiftOfCycle_eval]
  apply Cochain.ofHom_injective
  rw [mappingCone.ofHom_lift, complexConeShiftIso_hom_cochain]
  change mappingCone.liftCochain ((moduleEvaluation A D x).map (moduleShiftMap A D s f))
    ((moduleHomπ A D (shiftModule s (ForgetEnrichment.to (Complex A) (moduleCone A D f)))
      (shiftModule s (ForgetEnrichment.to (Complex A) M)) x).f 1 (moduleConeShiftFirst A D s f))
    ((moduleHomπ A D (shiftModule s (ForgetEnrichment.to (Complex A) (moduleCone A D f)))
      (shiftModule s (ForgetEnrichment.to (Complex A) N)) x).f 0 (moduleConeShiftSecond A D s f))
    (zero_add 1) = _
  rw [moduleConeShiftFirst_π, moduleConeShiftSecond_π]

@[simp] lemma moduleConeShiftInv_eval (s : ℤ) {M N : ModuleCategory A D} (f : M ⟶ N) (x : D) :
    (moduleEvaluation A D x).map (moduleConeShiftInv A D s f) =
      (complexConeShiftIso ((moduleEvaluation A D x).map f) s
        ((moduleEvaluation A D x).map (moduleShiftMap A D s f))
        (moduleShiftMap_eval A D s f x)).inv := by
  unfold moduleConeShiftInv
  rw [moduleConeDescOfBoundary_eval]
  apply Cochain.ofHom_injective
  rw [mappingCone.ofHom_desc, complexConeShiftIso_inv_cochain]
  change mappingCone.descCochain ((moduleEvaluation A D x).map (moduleShiftMap A D s f))
    ((moduleHomπ A D (shiftModule s (ForgetEnrichment.to (Complex A) M))
      (shiftModule s (ForgetEnrichment.to (Complex A) (moduleCone A D f))) x).f (-1)
        (moduleConeShiftLeftInput A D s f))
    (Cochain.ofHom ((moduleEvaluation A D x).map (moduleShiftMap A D s (moduleConeInr A D f))))
    (neg_add_cancel 1) = _
  rw [moduleConeShiftLeftInput_π, moduleShiftMap_eval A D s (moduleConeInr A D f) x,
    moduleConeInr_eval A D f x]

lemma moduleConeShift_hom_inv (s : ℤ) {M N : ModuleCategory A D} (f : M ⟶ N) :
    moduleConeShiftHom A D s f ≫ moduleConeShiftInv A D s f = 𝟙 _ := by
  apply moduleMorphism_ext
  intro x
  rw [CategoryTheory.Functor.map_comp, moduleConeShiftHom_eval, moduleConeShiftInv_eval,
    CategoryTheory.Functor.map_id, Iso.hom_inv_id]

lemma moduleConeShift_inv_hom (s : ℤ) {M N : ModuleCategory A D} (f : M ⟶ N) :
    moduleConeShiftInv A D s f ≫ moduleConeShiftHom A D s f = 𝟙 _ := by
  apply moduleMorphism_ext
  intro x
  rw [CategoryTheory.Functor.map_comp, moduleConeShiftInv_eval, moduleConeShiftHom_eval,
    CategoryTheory.Functor.map_id, Iso.inv_hom_id]

/-- 非有界dg加群のconeと任意整数shiftの、実際の加群圏での同型。 -/
def moduleConeShiftIso (s : ℤ) {M N : ModuleCategory A D} (f : M ⟶ N) :
    moduleShiftObj A D s (moduleCone A D f) ≅ moduleCone A D (moduleShiftMap A D s f) where
  hom := moduleConeShiftHom A D s f
  inv := moduleConeShiftInv A D s f
  hom_inv_id := moduleConeShift_hom_inv A D s f
  inv_hom_id := moduleConeShift_inv_hom A D s f

end SerrePositivity.DifferentialGraded
