module
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.Localization
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.ComplexCompletionReconstruction

/-! # Completion preserves all power-Koszul quotients along its standard unit

The scalar-cone functor preserves the standard reconstruction short exact sequence.
Its third term vanishes after any power-Koszul quotient, without regularity assumptions.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
namespace SerrePositivity.DerivedCompletion
open CategoryTheory CategoryTheory.Limits HomologicalComplex
attribute [local instance] HasDerivedCategory.standard
variable (R : Type u) [CommRing R] (a : R)

/-- The inclusion from the constant holim into completion becomes an isomorphism modulo Koszul. -/
lemma complexCompletionTowerInclusion_koszul_isIso
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℕ) :
    IsIso (DerivedCategory.Q.map
      ((scalarConeFunctor (a ^ n)).map (complexCompletionTowerInclusion R a K))) := by
  let hS := scalarConeFunctor_shortExact (a ^ n)
    (complexCompletionReconstructionSequence R a K)
    (complexCompletionReconstructionSequence_shortExact R a K)
  apply (CategoryTheory.Pretriangulated.Triangle.isZero₃_iff_isIso₁
    (DerivedCategory.triangleOfSES hS) (DerivedCategory.triangleOfSES_distinguished hS)).mp
  exact scalarComplexTowerHomotopyLimit_koszul_isZero R a (K⟦(1 : ℤ)⟧) n

/-- The standard completion unit preserves every power-Koszul quotient, for arbitrary complexes. -/
lemma complexCompletionUnit_koszul_quasiIso
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℕ) :
    QuasiIso ((scalarConeFunctor (a ^ n)).map (complexCompletionUnit R a K)) := by
  have := constantComplexTowerUnit_quasiIso R K
  have := scalarConeFunctor_map_quasiIso R (a ^ n) (constantComplexTowerUnit R K)
  have := (DerivedCategory.isIso_Q_map_iff_quasiIso (ModuleCat R) _).mp
    (complexCompletionTowerInclusion_koszul_isIso R a K n)
  rw [← constantComplexTowerUnit_comp_completionInclusion, CategoryTheory.Functor.map_comp]
  infer_instance

/-- The reduction isomorphism is the actual image of the standard completion unit. -/
def complexCompletionReductionIso (K : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℕ) :
    DerivedCategory.Q.obj (complexPowerKoszulStage R a K n) ≅
      DerivedCategory.Q.obj
        (complexPowerKoszulStage R a ((complexCompletionFunctor R a).obj K) n) := by
  have := complexCompletionUnit_koszul_quasiIso R a K n
  exact asIso (DerivedCategory.Q.map
    ((scalarConeFunctor (a ^ n)).map (complexCompletionUnit R a K)))

end SerrePositivity.DerivedCompletion
