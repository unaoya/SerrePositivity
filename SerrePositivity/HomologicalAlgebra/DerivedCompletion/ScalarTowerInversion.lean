module
public import SerrePositivity.CommutativeAlgebra.AdicRecurrenceInversion
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.LocalizationTowerComparison
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.MilnorSequence
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.ComplexCompletion

/-! # The scalar is invertible on its scalar-transition homotopy limit

The Milnor sequence retains both the limit and lim¹. On each, shifting sequences
inverts multiplication by the scalar. The short five lemma gives the same for holim.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
namespace SerrePositivity.DerivedCompletion
open CategoryTheory CategoryTheory.Limits HomologicalComplex
attribute [local instance] HasDerivedCategory.standard
variable (R : Type u) [CommRing R] (a : R) (K : CochainComplex (ModuleCat.{u} R) ℤ)

/-- On homology, the scalar-transition difference is the ordinary scalar recurrence. -/
lemma scalarComplexTowerHomologyDifference (i : ℤ) :
    complexTowerHomologyDifference R (constantComplexTower R K) (fun _ => smulId a K) i =
      adicRecurrenceMap (M := K.homology i) a := by
  apply LinearMap.ext
  intro x
  funext n
  change x n - homologyMap (smulId a K) i (x (n + 1)) = x n - a • x (n + 1)
  rw [smulId, homologyMap_smul, homologyMap_id]
  rfl

/-- Multiplication by the scalar is invertible on each homology group of the scalar holim. -/
lemma scalarComplexTowerHomotopyLimit_homology_smul_isIso (i : ℤ) :
    IsIso (a • 𝟙 (ModuleCat.of R ((scalarComplexTowerHomotopyLimit R a K).homology i))) := by
  let S := complexTowerMilnorSequence R (constantComplexTower R K) (fun _ => smulId a K) i
  let φ : S ⟶ S :=
    { τ₁ := a • 𝟙 S.X₁
      τ₂ := a • 𝟙 S.X₂
      τ₃ := a • 𝟙 S.X₃
      comm₁₂ := by simp
      comm₂₃ := by simp }
  have h₁ : IsIso φ.τ₁ := by
    apply (ConcreteCategory.isIso_iff_bijective _).mpr
    change Function.Bijective (fun x : complexTowerHomologyLimOne R
      (constantComplexTower R K) (fun _ => smulId a K) (i - 1) => a • x)
    have h (d : (ℕ → K.homology (i - 1)) →ₗ[R] (ℕ → K.homology (i - 1)))
        (hd : d = adicRecurrenceMap a) :
        Function.Bijective (fun x : (ℕ → K.homology (i - 1)) ⧸ d.range => a • x) := by
      subst d
      exact (adicRecurrenceCokernelScalarEquiv (M := K.homology (i - 1)) a).bijective
    exact h _ (scalarComplexTowerHomologyDifference R a K (i - 1))
  have h₃ : IsIso φ.τ₃ := by
    apply (ConcreteCategory.isIso_iff_bijective _).mpr
    change Function.Bijective (fun x : (complexTowerHomologyDifference R
      (constantComplexTower R K) (fun _ => smulId a K) i).ker => a • x)
    rw [scalarComplexTowerHomologyDifference]
    exact (adicRecurrenceKernelScalarEquiv (M := K.homology i) a).bijective
  have := h₁
  have := h₃
  exact ShortComplex.isIso₂_of_shortExact_of_isIso₁₃ φ
    (complexTowerMilnorSequence_shortExact R _ _ i)
    (complexTowerMilnorSequence_shortExact R _ _ i)

/-- Multiplication by the scalar is a quasi-isomorphism on the actual scalar holim complex. -/
lemma scalarComplexTowerHomotopyLimit_smul_quasiIso :
    QuasiIso (smulId a (scalarComplexTowerHomotopyLimit R a K)) := by
  rw [quasiIso_iff]
  intro i
  rw [quasiIsoAt_iff_isIso_homologyMap, smulId, homologyMap_smul, homologyMap_id]
  exact scalarComplexTowerHomotopyLimit_homology_smul_isIso R a K i

/-- The scalar action is invertible on the actual derived object of the scalar holim. -/
lemma scalarComplexTowerHomotopyLimit_smul_isIso :
    IsIso (DerivedCategory.Q.map (smulId a (scalarComplexTowerHomotopyLimit R a K))) := by
  have := scalarComplexTowerHomotopyLimit_smul_quasiIso R a K
  infer_instance

/-- Every nonnegative scalar power is a quasi-isomorphism on the scalar holim. -/
lemma scalarComplexTowerHomotopyLimit_pow_smul_quasiIso (n : ℕ) :
    QuasiIso (smulId (a ^ n) (scalarComplexTowerHomotopyLimit R a K)) := by
  induction n with
  | zero =>
    simp only [pow_zero, smulId, one_smul]
    infer_instance
  | succ n ih =>
    have he : smulId (a ^ (n + 1)) (scalarComplexTowerHomotopyLimit R a K) =
        smulId (a ^ n) (scalarComplexTowerHomotopyLimit R a K) ≫
          smulId a (scalarComplexTowerHomotopyLimit R a K) := by
      simp [smulId, pow_succ, smul_smul, mul_comm]
    rw [he]
    have := ih
    have := scalarComplexTowerHomotopyLimit_smul_quasiIso R a K
    infer_instance

/-- All power-Koszul quotients of the residual scalar holim vanish in the derived category. -/
lemma scalarComplexTowerHomotopyLimit_koszul_isZero (n : ℕ) :
    IsZero (DerivedCategory.Q.obj
      (complexPowerKoszulStage R a (scalarComplexTowerHomotopyLimit R a K) n)) := by
  have := scalarComplexTowerHomotopyLimit_pow_smul_quasiIso R a K n
  exact (CategoryTheory.Pretriangulated.Triangle.isZero₃_iff_isIso₁
    (DerivedCategory.Q.mapTriangle.obj (CochainComplex.mappingCone.triangle
      (smulId (a ^ n) (scalarComplexTowerHomotopyLimit R a K))))
    (DerivedCategory.mappingCone_triangle_distinguished _)).mpr (by
      change IsIso (DerivedCategory.Q.map (smulId (a ^ n) (scalarComplexTowerHomotopyLimit R a K)))
      infer_instance)

end SerrePositivity.DerivedCompletion
