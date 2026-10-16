module

public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.PowerImageTower
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.ConstantTower
public import Mathlib.Algebra.Homology.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact

/-! # Reconstruct complete flat complexes from their ordinary power cokernels -/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.DerivedCompletion
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped ZeroObject
attribute [local instance] HasDerivedCategory.standard
variable {R : Type u} [CommRing R] (a : R)
    (K : CochainComplex (ModuleCat.{u} R) ℤ)

/-- The torsion, scalar, and image towers form a short exact sequence after holim. -/
abbrev powerTorsionImageHolimShortComplex :
    ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ) :=
  complexTowerHomotopyLimitShortComplex R
    (powerTorsionComplexTransition a K) (fun _ ↦ smulId a K)
    (powerImageComplexTransition a K) (powerTorsionComplexInclusion a K)
    (fun n ↦ Abelian.factorThruImage (smulId (a ^ n) K))
    (powerTorsionComplexInclusion_transition a K) (powerImageComplexTransition_factor a K)
    (powerTorsionComplexInclusion_factor_zero a K)

lemma powerTorsionImageHolimShortComplex_shortExact :
    (powerTorsionImageHolimShortComplex a K).ShortExact :=
  complexTowerHomotopyLimitShortComplex_shortExact R _ _ _ _ _ _ _ _
    (powerTorsionImageShortComplex_shortExact a K)

/-- For a complete termwise flat complex, the holim of its actual image tower is acyclic. -/
theorem powerImageComplex_holim_acyclic (hK : ∀ i, Module.Flat R (K.X i))
    (N : ℕ) (h : ∀ n : ℕ, ∀ r : R, a ^ n * r = 0 → a ^ N * r = 0)
    (hc : IsComplete R a (DerivedCategory.Q.obj K)) :
    (complexTowerHomotopyLimit R (powerImageComplex a K)
      (powerImageComplexTransition a K)).Acyclic := by
  have hT := powerTorsionComplex_holim_acyclic a K hK N h
  have hS := scalarComplexTowerHomotopyLimit_acyclic_of_isComplete R a K hc
  have he := powerTorsionImageHolimShortComplex_shortExact a K
  intro i
  apply (exactAt_iff_isZero_homology _ i).mpr
  exact (he.homology_exact₃ i (i + 1) rfl).isZero_of_both_isZero
    (hS i).isZero_homology (hT (i + 1)).isZero_homology

@[reassoc] lemma powerCokernelComplexTransition_π (n : ℕ) :
    cokernel.π (smulId (a ^ (n + 1)) K) ≫ powerCokernelComplexTransition a K n =
      cokernel.π (smulId (a ^ n) K) := by
  simp [powerCokernelComplexTransition]

/-- The image, constant, and ordinary cokernel towers form a short exact sequence after holim. -/
abbrev powerImageCokernelHolimShortComplex :
    ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ) :=
  complexTowerHomotopyLimitShortComplex R
    (powerImageComplexTransition a K) (fun _ ↦ 𝟙 K) (powerCokernelComplexTransition a K)
    (fun n ↦ Abelian.image.ι (smulId (a ^ n) K)) (fun n ↦ cokernel.π (smulId (a ^ n) K))
    (fun n ↦ by simpa using powerImageComplexTransition_ι a K n)
    (fun n ↦ by simpa using (powerCokernelComplexTransition_π a K n).symm)
    (fun n ↦ kernel.condition _)

lemma powerImageCokernelHolimShortComplex_shortExact :
    (powerImageCokernelHolimShortComplex a K).ShortExact :=
  complexTowerHomotopyLimitShortComplex_shortExact R _ _ _ _ _ _ _ _
    (powerImageCokernelShortComplex_shortExact a K)

/-- The canonical map from a complex to the holim of its ordinary power cokernels. -/
def powerCokernelReconstruction :
    K ⟶ complexTowerHomotopyLimit R (powerCokernelComplex a K)
      (powerCokernelComplexTransition a K) :=
  constantComplexTowerUnit R K ≫ (powerImageCokernelHolimShortComplex a K).g

/-- The reconstruction uses the original quotient maps at every stage. -/
lemma powerCokernelReconstruction_eq_lift :
    powerCokernelReconstruction a K =
      complexTowerCompatibleLift R (powerCokernelComplex a K) (powerCokernelComplexTransition a K)
        K (fun n ↦ cokernel.π (smulId (a ^ n) K))
        (powerCokernelComplexTransition_π a K) := by
  unfold powerCokernelReconstruction constantComplexTowerUnit
  apply complexTowerCompatibleLift_map
  intro n
  simp

@[reassoc] lemma powerCokernelReconstruction_projection (n : ℕ) :
    powerCokernelReconstruction a K ≫
      complexTowerProjection R (powerCokernelComplex a K) (powerCokernelComplexTransition a K) ≫
        Pi.π (powerCokernelComplex a K) n = cokernel.π (smulId (a ^ n) K) := by
  rw [powerCokernelReconstruction_eq_lift, ← Category.assoc,
    complexTowerCompatibleLift_comp_projection, Pi.lift_comp_π]

/-- With bounded ring torsion, this actual standard map is a quasi-isomorphism
for every complete termwise flat complex. -/
theorem powerCokernelReconstruction_quasiIso (hK : ∀ i, Module.Flat R (K.X i))
    (N : ℕ) (h : ∀ n : ℕ, ∀ r : R, a ^ n * r = 0 → a ^ N * r = 0)
    (hc : IsComplete R a (DerivedCategory.Q.obj K)) :
    QuasiIso (powerCokernelReconstruction a K) := by
  have hJ := powerImageComplex_holim_acyclic a K hK N h hc
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

end SerrePositivity.DerivedCompletion
