module

public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.KoszulPowerCokernelComparison

/-! # Ordinary power quotient reconstruction with a bound on the terms

The original ring need not have bounded torsion and the terms need not be flat.
The specified common bound on their power torsion kills the actual error tower.
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.DerivedCompletion
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped ZeroObject
attribute [local instance] HasDerivedCategory.standard
variable {R : Type u} [CommRing R] (a : R)
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (N : ℕ)
    (h : ∀ (i : ℤ) (n : ℕ) (x : K.X i), a ^ n • x = 0 → a ^ N • x = 0)

include N h

/-- A common termwise bound kills the genuine torsion tower, with its scalar
transitions rather than inclusion maps. -/
lemma powerTorsionComplex_holim_acyclic_of_term_bound :
    (complexTowerHomotopyLimit R (powerTorsionComplex a K)
      (powerTorsionComplexTransition a K)).Acyclic := by
  apply complexTowerHolim_acyclic_of_uniform_zero R _ _ N
  intro n
  apply HomologicalComplex.Hom.ext
  funext i
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  change (((complexTowerComposite R (powerTorsionComplex a K)
    (powerTorsionComplexTransition a K) n N).f i x :
    (powerTorsionComplex a K n).X i) : K.X i) = 0
  rw [powerTorsionComplexComposite_coe]
  exact h i (n + N) x x.property

lemma powerImageComplex_holim_acyclic_of_term_bound
    (hc : IsComplete R a (DerivedCategory.Q.obj K)) :
    (complexTowerHomotopyLimit R (powerImageComplex a K)
      (powerImageComplexTransition a K)).Acyclic := by
  have hT := powerTorsionComplex_holim_acyclic_of_term_bound a K N h
  have hS := scalarComplexTowerHomotopyLimit_acyclic_of_isComplete R a K hc
  have he := powerTorsionImageHolimShortComplex_shortExact a K
  intro i
  exact (exactAt_iff_isZero_homology _ i).mpr
    ((he.homology_exact₃ i (i + 1) rfl).isZero_of_both_isZero
      (hS i).isZero_homology (hT (i + 1)).isZero_homology)

/-- The original quotient reconstruction is a quasi-isomorphism for a complete
complex with a common termwise power-torsion bound. -/
lemma powerCokernelReconstruction_quasiIso_of_term_bound
    (hc : IsComplete R a (DerivedCategory.Q.obj K)) :
    QuasiIso (powerCokernelReconstruction a K) := by
  have hJ := powerImageComplex_holim_acyclic_of_term_bound a K N h hc
  let S := powerImageCokernelHolimShortComplex a K
  have hS := powerImageCokernelHolimShortComplex_shortExact a K
  have hz : IsZero (DerivedCategory.Q.obj S.X₁) := by
    have hzero := HomologicalComplex.acyclic_of_isZero
      (0 : CochainComplex (ModuleCat.{u} R) ℤ)
      (isZero_zero (CochainComplex (ModuleCat.{u} R) ℤ))
    have : QuasiIso (0 : S.X₁ ⟶ 0) := by
      rw [quasiIso_iff]
      intro i
      exact (quasiIsoAt_iff_exactAt _ i (hJ i)).mpr (hzero i)
    exact (DerivedCategory.Q.map_isZero (isZero_zero _)).of_iso
      (asIso (DerivedCategory.Q.map (0 : S.X₁ ⟶ 0)))
  have hg : IsIso (DerivedCategory.Q.map S.g) :=
    (CategoryTheory.Pretriangulated.Triangle.isZero₁_iff_isIso₂
      (DerivedCategory.triangleOfSES hS) (DerivedCategory.triangleOfSES_distinguished hS)).mp hz
  have : QuasiIso S.g := (DerivedCategory.isIso_Q_map_iff_quasiIso (ModuleCat R) _).mp hg
  have := constantComplexTowerUnit_quasiIso R K
  exact inferInstanceAs (QuasiIso (constantComplexTowerUnit R K ≫ S.g))

/-- The existing standard augmentation of towers is a quasi-isomorphism, with
the existing completion unit diagram retained. -/
lemma koszulPowerCokernelComparison_quasiIso_of_term_bound
    (hc : IsComplete R a (DerivedCategory.Q.obj K)) :
    QuasiIso (koszulPowerCokernelComparison a K) := by
  have := complexCompletionUnit_quasiIso_of_isComplete R a K hc
  have : QuasiIso (complexCompletionUnit R a K ≫ koszulPowerCokernelComparison a K) := by
    rw [complexCompletionUnit_comp_koszulPowerCokernelComparison]
    exact powerCokernelReconstruction_quasiIso_of_term_bound a K N h hc
  exact (quasiIso_iff_comp_left (complexCompletionUnit R a K) _).mp inferInstance

end SerrePositivity.DerivedCompletion
