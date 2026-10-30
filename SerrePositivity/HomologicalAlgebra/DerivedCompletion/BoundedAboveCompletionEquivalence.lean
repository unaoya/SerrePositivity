module

public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.ComplexCompletionReflection
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.DerivedKoszulReduction
public import SerrePositivity.HomologicalAlgebra.BoundedAbove.Derived

/-! # Detecting derived completion equivalences by power-Koszul reductions -/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.DerivedCompletion
open CategoryTheory HomologicalComplex
attribute [local instance] HasDerivedCategory.standard
variable (R : Type u) [CommRing R] (a : R)

/-- If completion inverts a morphism, every power-Koszul reduction inverts it. -/
theorem derivedScalarCone_map_isIso_of_completion
    {X Y : ConcreteDerivedCategory R} (f : X ⟶ Y)
    (hf : IsIso ((derivedComplexCompletionFunctor R a).map f)) (n : ℕ) :
    IsIso ((derivedScalarConeFunctor R (a ^ n)).map f) := by
  have := hf
  let G := derivedScalarConeFunctor R (a ^ n)
  let μ := derivedComplexCompletionReduction R a n
  have := derivedComplexCompletionReduction_isIso R a n X
  have := derivedComplexCompletionReduction_isIso R a n Y
  have : IsIso (G.map f ≫ μ.app Y) := by
    rw [μ.naturality f]
    change IsIso (μ.app X ≫ G.map ((derivedComplexCompletionFunctor R a).map f))
    infer_instance
  exact IsIso.of_isIso_comp_right (G.map f) (μ.app Y)

/-- For bounded-above objects, power-Koszul equivalences become completion equivalences. -/
theorem boundedAboveCompletion_map_isIso_of_koszul
    {X Y : DerivedCategory.Minus (ModuleCat.{u} R)} (f : X ⟶ Y)
    (hf : ∀ n : ℕ, IsIso ((derivedScalarConeFunctor R (a ^ n)).map f.hom)) :
    IsIso ((derivedComplexCompletionFunctor R a).map f.hom) := by
  let P := boundedAboveDerivedChosenModel X
  let Q := boundedAboveDerivedChosenModel Y
  let h := P.map Q f.hom
  have hk (n : ℕ) : QuasiIso ((scalarConeFunctor (a ^ n)).map h) := by
    apply (DerivedCategory.isIso_Q_map_iff_quasiIso (ModuleCat R) _).mp
    apply (NatIso.isIso_map_iff (derivedScalarConeComparison R (a ^ n)) h).mp
    change IsIso ((derivedScalarConeFunctor R (a ^ n)).map (DerivedCategory.Q.map h))
    dsimp only [h]
    rw [P.map_Q, Functor.map_comp, Functor.map_comp]
    have := hf n
    infer_instance
  have := complexCompletionFunctor_map_quasiIso_of_koszul R a h hk
  have ht : IsIso ((derivedComplexCompletionFunctor R a).map (DerivedCategory.Q.map h)) :=
    (NatIso.isIso_map_iff (derivedComplexCompletionComparison R a) h).mpr (by
      change IsIso (DerivedCategory.Q.map ((complexCompletionFunctor R a).map h))
      infer_instance)
  dsimp only [h] at ht
  rw [P.map_Q, Functor.map_comp, Functor.map_comp] at ht
  have hs : IsIso ((derivedComplexCompletionFunctor R a).map f.hom ≫
      (derivedComplexCompletionFunctor R a).map Q.iso.inv) :=
    IsIso.of_isIso_comp_left ((derivedComplexCompletionFunctor R a).map P.iso.hom) _
  exact IsIso.of_isIso_comp_right _ ((derivedComplexCompletionFunctor R a).map Q.iso.inv)

/-- The actual completion equivalences are precisely the power-Koszul equivalences on D⁻. -/
theorem boundedAboveCompletion_map_isIso_iff_koszul
    {X Y : DerivedCategory.Minus (ModuleCat.{u} R)} (f : X ⟶ Y) :
    IsIso ((derivedComplexCompletionFunctor R a).map f.hom) ↔
      ∀ n : ℕ, IsIso ((derivedScalarConeFunctor R (a ^ n)).map f.hom) :=
  ⟨fun hf n ↦ derivedScalarCone_map_isIso_of_completion R a f.hom hf n,
    boundedAboveCompletion_map_isIso_of_koszul R a f⟩

/-- Power-Koszul equivalences between complete bounded-above objects are actual isomorphisms. -/
theorem boundedAbove_isIso_of_koszul_of_isComplete
    {X Y : DerivedCategory.Minus (ModuleCat.{u} R)} (f : X ⟶ Y)
    (hX : IsComplete R a X.obj) (hY : IsComplete R a Y.obj)
    (hf : ∀ n : ℕ, IsIso ((derivedScalarConeFunctor R (a ^ n)).map f.hom)) :
    IsIso f := by
  have := boundedAboveCompletion_map_isIso_of_koszul R a f hf
  have := derivedComplexCompletionUnit_isIso_of_isComplete R a X.obj hX
  have := derivedComplexCompletionUnit_isIso_of_isComplete R a Y.obj hY
  have : IsIso (f.hom ≫ (derivedComplexCompletionUnit R a).app Y.obj) := by
    have hn := (derivedComplexCompletionUnit R a).naturality f.hom
    change f.hom ≫ (derivedComplexCompletionUnit R a).app Y.obj =
      (derivedComplexCompletionUnit R a).app X.obj ≫
        (derivedComplexCompletionFunctor R a).map f.hom at hn
    rw [hn]
    infer_instance
  have : IsIso f.hom := IsIso.of_isIso_comp_right _
    ((derivedComplexCompletionUnit R a).app Y.obj)
  have : IsIso (DerivedCategory.Minus.ι.map f) := this
  exact isIso_of_reflects_iso f DerivedCategory.Minus.ι

end SerrePositivity.DerivedCompletion
