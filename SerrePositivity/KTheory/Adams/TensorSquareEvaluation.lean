module

public import SerrePositivity.KTheory.Adams.TensorSquareAcyclicClass
public import SerrePositivity.KTheory.Adams.TensorSquareMaps

/-! # The tensor-square evaluation on supported homotopy objects -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u

namespace SerrePositivity
open CategoryTheory Category Limits Pretriangulated
variable {R : Type u} [CommRing R] [Invertible (2 : R)]

namespace Adams
variable (Z : TopologicalSpace.Closeds (PrimeSpectrum R))

lemma tensorSquareClass_eq_of_quasiIso
    {P Q : CochainComplex (ModuleCat.{u} R) ℤ}
    (hp : strictlyPerfectComplex R P) (hq : strictlyPerfectComplex R Q)
    (hsP : HasHomologySupportOn Z P) (hsQ : HasHomologySupportOn Z Q)
    (f : P ⟶ Q) [QuasiIso f] :
    tensorSquareClass P Z hp hsP = tensorSquareClass Q Z hq hsQ := by
  have := tensorSquarePositiveMap_quasiIso f hp hq
  have := tensorSquareNegativeMap_quasiIso f hp hq
  have hpos := K0WithSupport.mk_eq_of_quasiIso Z (tensorSquarePositive P) (tensorSquarePositive Q)
    (tensorSquarePositive_perfect P hp) (tensorSquarePositive_perfect Q hq)
    (tensorSquarePositive_support hp hsP) (tensorSquarePositive_support hq hsQ)
    (tensorSquarePositiveMap f)
  have hneg := K0WithSupport.mk_eq_of_quasiIso Z (tensorSquareNegative P) (tensorSquareNegative Q)
    (tensorSquareNegative_perfect P hp) (tensorSquareNegative_perfect Q hq)
    (tensorSquareNegative_support hp hsP) (tensorSquareNegative_support hq hsQ)
    (tensorSquareNegativeMap f)
  exact congrArg₂ (fun x y : K0WithSupport Z => x - y) hpos hneg

lemma tensorSquareClass_eq_of_homotopyEquiv
    {P Q : CochainComplex (ModuleCat.{u} R) ℤ}
    (hp : strictlyPerfectComplex R P) (hq : strictlyPerfectComplex R Q)
    (hsP : HasHomologySupportOn Z P) (hsQ : HasHomologySupportOn Z Q)
    (e : HomotopyEquiv P Q) :
    tensorSquareClass P Z hp hsP = tensorSquareClass Q Z hq hsQ := by
  have : QuasiIso e.hom := (strictlyPerfectComplex_quasiIso_iff hp hq e.hom).mpr ⟨e, rfl⟩
  exact tensorSquareClass_eq_of_quasiIso Z hp hq hsP hsQ e.hom

/-- Evaluate a supported homotopy object by the difference of tensor-square eigenspaces. -/
def tensorSquareEvaluation (X : SupportedPerfectHomotopyOn Z) : K0WithSupport Z :=
  tensorSquareClass (supportedPerfectRepresentative X) Z
    (supportedPerfectRepresentative_perfect X) (supportedPerfectRepresentative_support X)

@[simp]
lemma tensorSquareEvaluation_concrete (P : CochainComplex (ModuleCat.{u} R) ℤ)
    (hp : strictlyPerfectComplex R P) (hs : HasHomologySupportOn Z P) :
    tensorSquareEvaluation Z (supportedPerfectOnObj Z P hp hs) = tensorSquareClass P Z hp hs := rfl

lemma tensorSquareEvaluation_iso {X Y : SupportedPerfectHomotopyOn Z} (e : X ≅ Y) :
    tensorSquareEvaluation Z X = tensorSquareEvaluation Z Y :=
  tensorSquareClass_eq_of_homotopyEquiv Z
    (supportedPerfectRepresentative_perfect X) (supportedPerfectRepresentative_perfect Y)
    (supportedPerfectRepresentative_support X) (supportedPerfectRepresentative_support Y)
    (HomotopyCategory.homotopyEquivOfIso
      ((supportedPerfectOnInclusion Z ⋙ perfectHomotopyInclusion R).mapIso e))

lemma tensorSquareEvaluation_shortExactAdditive :
    ClosedSupportShortExactAdditive Z (tensorSquareEvaluation Z) := by
  intro S hS h₁ h₂ h₃ s₁ s₂ s₃
  exact tensorSquareClass_shortExact Z S hS h₁ h₂ h₃ s₁ s₂ s₃

lemma tensorSquareClass_shift_one (P : CochainComplex (ModuleCat.{u} R) ℤ)
    (hp : strictlyPerfectComplex R P) (hs : HasHomologySupportOn Z P) :
    tensorSquareClass (P⟦(1 : ℤ)⟧) Z (strictlyPerfectComplex_shift hp 1) (hs.shift 1) =
      -tensorSquareClass P Z hp hs :=
  (tensorSquareEvaluation_shortExactAdditive Z).shift_one
    (tensorSquareEvaluation_iso Z) P hp hs

lemma tensorSquareClass_cone
    (P Q : CochainComplex (ModuleCat.{u} R) ℤ)
    (hp : strictlyPerfectComplex R P) (hq : strictlyPerfectComplex R Q)
    (hsP : HasHomologySupportOn Z P) (hsQ : HasHomologySupportOn Z Q) (f : P ⟶ Q) :
    tensorSquareClass (CochainComplex.mappingCone f) Z
      (strictlyPerfectComplex_mappingCone R f hp hq) (hsP.mappingCone f hsQ) =
      tensorSquareClass Q Z hq hsQ - tensorSquareClass P Z hp hsP :=
  (tensorSquareEvaluation_shortExactAdditive Z).cone (tensorSquareEvaluation_iso Z)
    P Q hp hq hsP hsQ f

lemma tensorSquareEvaluation_triangle
    (T : Triangle (SupportedPerfectHomotopyOn Z)) (hT : T ∈ distTriang _) :
    tensorSquareEvaluation Z T.obj₂ =
      tensorSquareEvaluation Z T.obj₁ + tensorSquareEvaluation Z T.obj₃ :=
  (tensorSquareEvaluation_shortExactAdditive Z).triangle (tensorSquareEvaluation_iso Z) T hT

end Adams
end SerrePositivity
