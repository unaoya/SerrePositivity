module

public import SerrePositivity.KTheory.Adams.TensorCubeAdditivity
public import SerrePositivity.KTheory.Adams.TensorCubeMaps
public import SerrePositivity.PerfectComplex.CubicActionClassMaps

/-! # The weighted tensor-cube evaluation on supported homotopy objects -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity
open CategoryTheory Category Limits Pretriangulated
variable {R : Type u} [CommRing R] [Invertible (3 : R)]
namespace Adams
variable (E : Type v) [CommRing E] (t : R) (ht : t ^ 2 + t + 1 = 0) (ζ : E)
variable (Z : TopologicalSpace.Closeds (PrimeSpectrum R))

lemma tensorCubeClass_eq_of_quasiIso
    {P Q : CochainComplex (ModuleCat.{u} R) ℤ}
    (hp : strictlyPerfectComplex R P) (hq : strictlyPerfectComplex R Q)
    (hsP : HasHomologySupportOn Z P) (hsQ : HasHomologySupportOn Z Q)
    (f : P ⟶ Q) [QuasiIso f] :
    tensorCubeClass E t ht ζ P Z hp hsP = tensorCubeClass E t ht ζ Q Z hq hsQ := by
  have := tensorCubeMap_quasiIso f hp hq
  exact CochainCubicAction.weightedK0Class_eq_of_quasiIso E
    (tensorCubeAction P) (tensorCubeAction Q) (tensorCubeMap f)
    (tensorCubeRotation_naturality f).symm t ht ζ Z
    (tensorCube_perfect P hp) (tensorCube_perfect Q hq)
    (tensorCube_support hp hsP) (tensorCube_support hq hsQ)

lemma tensorCubeClass_eq_of_homotopyEquiv
    {P Q : CochainComplex (ModuleCat.{u} R) ℤ}
    (hp : strictlyPerfectComplex R P) (hq : strictlyPerfectComplex R Q)
    (hsP : HasHomologySupportOn Z P) (hsQ : HasHomologySupportOn Z Q)
    (e : HomotopyEquiv P Q) :
    tensorCubeClass E t ht ζ P Z hp hsP = tensorCubeClass E t ht ζ Q Z hq hsQ := by
  have : QuasiIso e.hom := (strictlyPerfectComplex_quasiIso_iff hp hq e.hom).mpr ⟨e, rfl⟩
  exact tensorCubeClass_eq_of_quasiIso E t ht ζ Z hp hq hsP hsQ e.hom

lemma tensorCubeClass_eq_zero_of_acyclic
    (P : CochainComplex (ModuleCat.{u} R) ℤ)
    (hp : strictlyPerfectComplex R P) (hs : HasHomologySupportOn Z P) (hac : P.Acyclic) :
    tensorCubeClass E t ht ζ P Z hp hs = 0 := by
  have hc : (tensorCube P).Acyclic := (cochainAcyclic_iff_support_bot _).mpr
    (tensorCube_support hp ((cochainAcyclic_iff_support_bot P).mp hac))
  exact (tensorCubeAction P).weightedK0Class_eq_zero_of_acyclic E t ht ζ Z
    (tensorCube_perfect P hp) (tensorCube_support hp hs) hc

/-- Evaluate a supported homotopy object by its weighted cubic eigenspaces. -/
def tensorCubeEvaluation (X : SupportedPerfectHomotopyOn Z) : K0WithSupport.Coefficients E Z :=
  tensorCubeClass E t ht ζ (supportedPerfectRepresentative X) Z
    (supportedPerfectRepresentative_perfect X) (supportedPerfectRepresentative_support X)

@[simp]
lemma tensorCubeEvaluation_concrete (P : CochainComplex (ModuleCat.{u} R) ℤ)
    (hp : strictlyPerfectComplex R P) (hs : HasHomologySupportOn Z P) :
    tensorCubeEvaluation E t ht ζ Z (supportedPerfectOnObj Z P hp hs) =
      tensorCubeClass E t ht ζ P Z hp hs := rfl

lemma tensorCubeEvaluation_iso {X Y : SupportedPerfectHomotopyOn Z} (e : X ≅ Y) :
    tensorCubeEvaluation E t ht ζ Z X = tensorCubeEvaluation E t ht ζ Z Y :=
  tensorCubeClass_eq_of_homotopyEquiv E t ht ζ Z
    (supportedPerfectRepresentative_perfect X) (supportedPerfectRepresentative_perfect Y)
    (supportedPerfectRepresentative_support X) (supportedPerfectRepresentative_support Y)
    (HomotopyCategory.homotopyEquivOfIso
      ((supportedPerfectOnInclusion Z ⋙ perfectHomotopyInclusion R).mapIso e))

lemma tensorCubeEvaluation_shortExactAdditive (hζ : ζ ^ 2 + ζ + 1 = 0) :
    ClosedSupportShortExactAdditive Z (tensorCubeEvaluation E t ht ζ Z) := by
  intro S hS h₁ h₂ h₃ s₁ s₂ s₃
  exact tensorCubeClass_shortExact E t ht ζ hζ Z S hS h₁ h₂ h₃ s₁ s₂ s₃

lemma tensorCubeClass_shift_one (hζ : ζ ^ 2 + ζ + 1 = 0)
    (P : CochainComplex (ModuleCat.{u} R) ℤ)
    (hp : strictlyPerfectComplex R P) (hs : HasHomologySupportOn Z P) :
    tensorCubeClass E t ht ζ (P⟦(1 : ℤ)⟧) Z
      (strictlyPerfectComplex_shift hp 1) (hs.shift 1) = -tensorCubeClass E t ht ζ P Z hp hs :=
  (tensorCubeEvaluation_shortExactAdditive E t ht ζ Z hζ).shift_one
    (tensorCubeEvaluation_iso E t ht ζ Z) P hp hs

lemma tensorCubeClass_cone (hζ : ζ ^ 2 + ζ + 1 = 0)
    (P Q : CochainComplex (ModuleCat.{u} R) ℤ)
    (hp : strictlyPerfectComplex R P) (hq : strictlyPerfectComplex R Q)
    (hsP : HasHomologySupportOn Z P) (hsQ : HasHomologySupportOn Z Q) (f : P ⟶ Q) :
    tensorCubeClass E t ht ζ (CochainComplex.mappingCone f) Z
      (strictlyPerfectComplex_mappingCone R f hp hq) (hsP.mappingCone f hsQ) =
      tensorCubeClass E t ht ζ Q Z hq hsQ - tensorCubeClass E t ht ζ P Z hp hsP :=
  (tensorCubeEvaluation_shortExactAdditive E t ht ζ Z hζ).cone
    (tensorCubeEvaluation_iso E t ht ζ Z) P Q hp hq hsP hsQ f

lemma tensorCubeEvaluation_triangle (hζ : ζ ^ 2 + ζ + 1 = 0)
    (T : Triangle (SupportedPerfectHomotopyOn Z)) (hT : T ∈ distTriang _) :
    tensorCubeEvaluation E t ht ζ Z T.obj₂ =
      tensorCubeEvaluation E t ht ζ Z T.obj₁ + tensorCubeEvaluation E t ht ζ Z T.obj₃ :=
  (tensorCubeEvaluation_shortExactAdditive E t ht ζ Z hζ).triangle
    (tensorCubeEvaluation_iso E t ht ζ Z) T hT

end Adams
end SerrePositivity
