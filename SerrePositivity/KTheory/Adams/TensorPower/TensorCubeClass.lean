module

public import SerrePositivity.PerfectComplex.Eigen.Cubic
public import SerrePositivity.KTheory.Adams.TensorPower.TensorCubeLowMixed
public import SerrePositivity.KTheory.Adams.TensorPower.TensorCubeHighMixed
public import SerrePositivity.PerfectComplex.Tensor.CyclicSum
public import SerrePositivity.PerfectComplex.Eigen.CubicClass
public import SerrePositivity.PerfectComplex.ClosedSupport.Cup
public import SerrePositivity.KTheory.Adams.TensorPower.TensorCube

/-! # 重み付きの巡回テンソル三乗の類

## 概要

フィルトレーションの両方の混合層の打ち消しを示し、重み付きの巡回テンソル三乗の類が短完全列で加法的であることと、台つきホモトピー対象の上の重み付きテンソル三乗の評価を与える。

## 方針

各層の類を 1 の三乗根の重みで足し、混合層は巡回作用で打ち消す。

## 規約

`tensorCubeEvaluation*`・`tensorCubeClass` の名前は残す。

## 使われ方

`Adams/CyclicThree`。
-/

@[expose] public noncomputable section

universe u v

section TensorCubeMixedCancellationPart

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity
open CategoryTheory
namespace Adams
variable {R : Type u} [CommRing R] [Invertible (3 : R)]
variable (E : Type v) [CommRing E]
variable (S : ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ))
variable (t : R) (ht : t ^ 2 + t + 1 = 0) (ζ : E)
variable (Z : TopologicalSpace.Closeds (PrimeSpectrum R))

lemma tensorCubeLowMixed_weightedK0Class_eq_zero
    (ha : strictlyPerfectComplex R S.X₁) (hd : strictlyPerfectComplex R S.X₃)
    (hsA : HasHomologySupportOn Z S.X₁) (hsD : HasHomologySupportOn Z S.X₃)
    (hζ : ζ ^ 2 + ζ + 1 = 0) :
    (tensorCubeLowMixedAction S).weightedK0Class E t ht ζ Z
      (tensorCubeLowMixedTarget_perfect S ha hd)
      (tensorCubeLowMixedTarget_support S ha hd hsA hsD) = 0 :=
  cochainTensorCyclicSum_weightedK0Class_eq_zero S.X₃ S.X₁ S.X₁ t ht Z
    hd ha ha hsD hsA hsA E ζ hζ

lemma tensorCubeHighMixed_weightedK0Class_eq_zero
    (ha : strictlyPerfectComplex R S.X₁) (hd : strictlyPerfectComplex R S.X₃)
    (hsA : HasHomologySupportOn Z S.X₁) (hsD : HasHomologySupportOn Z S.X₃)
    (hζ : ζ ^ 2 + ζ + 1 = 0) :
    (tensorCubeHighMixedAction S).weightedK0Class E t ht ζ Z
      (tensorCubeHighMixedTarget_perfect S ha hd)
      (tensorCubeHighMixedTarget_support S ha hd hsA hsD) = 0 :=
  cochainTensorCyclicSum_weightedK0Class_eq_zero S.X₃ S.X₃ S.X₁ t ht Z
    hd hd ha hsD hsD hsA E ζ hζ

end Adams
end SerrePositivity

end TensorCubeMixedCancellationPart

section TensorCubeAdditivityPart

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity
open CategoryTheory Category Limits
namespace Adams
variable {R : Type u} [CommRing R] [Invertible (3 : R)]

/-- The cubic eigenspace classes weighted by a root in the coefficient ring. -/
def tensorCubeClass (E : Type v) [CommRing E] (t : R) (ht : t ^ 2 + t + 1 = 0) (ζ : E)
    (P : CochainComplex (ModuleCat.{u} R) ℤ) (Z : TopologicalSpace.Closeds (PrimeSpectrum R))
    (hp : strictlyPerfectComplex R P) (hs : HasHomologySupportOn Z P) :
    K0WithSupport.Coefficients E Z :=
  (tensorCubeAction P).weightedK0Class E t ht ζ Z
    (tensorCube_perfect P hp) (tensorCube_support hp hs)

set_option backward.isDefEq.respectTransparency true in
set_option maxHeartbeats 1200000 in
-- The three filtered sequences cumulatively normalize tensor, kernel and biproduct models.
lemma tensorCubeClass_shortExact (E : Type v) [CommRing E]
    (t : R) (ht : t ^ 2 + t + 1 = 0) (ζ : E) (hζ : ζ ^ 2 + ζ + 1 = 0)
    (Z : TopologicalSpace.Closeds (PrimeSpectrum R))
    (S : ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ)) (hS : S.ShortExact)
    (ha : strictlyPerfectComplex R S.X₁) (hp : strictlyPerfectComplex R S.X₂)
    (hd : strictlyPerfectComplex R S.X₃)
    (hsA : HasHomologySupportOn Z S.X₁) (hsP : HasHomologySupportOn Z S.X₂)
    (hsD : HasHomologySupportOn Z S.X₃) :
    tensorCubeClass E t ht ζ S.X₂ Z hp hsP =
      tensorCubeClass E t ht ζ S.X₁ Z ha hsA + tensorCubeClass E t ht ζ S.X₃ Z hd hsD := by
  let hproj := fun i => (hd.2 i).2
  have hout := CochainCubicAction.weightedK0Class_shortExact
    (tensorCubeKernelShortComplex S.g) (tensorCubeKernelAction S.g)
    (tensorCubeAction S.X₂) (tensorCubeAction S.X₃)
    (tensorCubeKernelRotation_inclusion S.g) (tensorCubeRotation_naturality S.g).symm t ht
    E ζ Z (tensorCubeKernelShortComplex_shortExact S hS hproj)
    (tensorCubeKernel_perfect S hS hp hd) (tensorCube_perfect S.X₂ hp)
    (tensorCube_perfect S.X₃ hd) (tensorCubeKernel_support S hS hp hd hsP hsD)
    (tensorCube_support hp hsP) (tensorCube_support hd hsD)
  have hhigh := CochainCubicAction.weightedK0Class_shortExact
    (tensorCubeHighMixedShortComplex S hS hproj) (tensorCubeFirstLayerAction S.g)
    (tensorCubeKernelAction S.g) (tensorCubeHighMixedAction S)
    (by
      dsimp only [tensorCubeHighMixedShortComplex, tensorCubeFirstLayerAction,
        tensorCubeKernelAction]
      exact (tensorCubeFirstLayerToKernel_rotation S.g).symm)
    (by
      dsimp only [tensorCubeHighMixedShortComplex, tensorCubeKernelAction,
        tensorCubeHighMixedAction, cochainTensorCyclicSumAction]
      exact tensorCubeHighMixedMap_rotation S hS hproj) t ht E ζ Z
    (tensorCubeHighMixedShortComplex_shortExact S hS hproj)
    (tensorCubeFirstLayer_perfect S hS hp hd) (tensorCubeKernel_perfect S hS hp hd)
    (tensorCubeHighMixedTarget_perfect S ha hd) (tensorCubeFirstLayer_support S hS ha hd hsA hsD)
    (tensorCubeKernel_support S hS hp hd hsP hsD)
    (tensorCubeHighMixedTarget_support S ha hd hsA hsD)
  have hlow := CochainCubicAction.weightedK0Class_shortExact
    (tensorCubeLowMixedShortComplex S hS hproj) (tensorCubeAction S.X₁)
    (tensorCubeFirstLayerAction S.g) (tensorCubeLowMixedAction S)
    (by
      dsimp only [tensorCubeLowMixedShortComplex, tensorCubeAction, tensorCubeFirstLayerAction]
      exact (tensorCubeFirstLayerFirstMap_rotation S).symm)
    (by
      dsimp only [tensorCubeLowMixedShortComplex, tensorCubeFirstLayerAction,
        tensorCubeLowMixedAction, cochainTensorCyclicSumAction]
      exact tensorCubeLowMixedMap_rotation S hS hproj)
    t ht E ζ Z (tensorCubeLowMixedShortComplex_shortExact S hS hproj)
    (tensorCube_perfect S.X₁ ha) (tensorCubeFirstLayer_perfect S hS hp hd)
    (tensorCubeLowMixedTarget_perfect S ha hd) (tensorCube_support ha hsA)
    (tensorCubeFirstLayer_support S hS ha hd hsA hsD)
    (tensorCubeLowMixedTarget_support S ha hd hsA hsD)
  dsimp only [tensorCubeKernelShortComplex, tensorCubeHighMixedShortComplex,
    tensorCubeLowMixedShortComplex] at hout hhigh hlow
  dsimp only [tensorCubeClass]
  rw [hout, hhigh, hlow,
    tensorCubeLowMixed_weightedK0Class_eq_zero E S t ht ζ Z ha hd hsA hsD hζ,
    tensorCubeHighMixed_weightedK0Class_eq_zero E S t ht ζ Z ha hd hsA hsD hζ,
    add_zero, add_zero]

end Adams
end SerrePositivity

end TensorCubeAdditivityPart

section TensorCubeEvaluationPart

set_option backward.isDefEq.respectTransparency false
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

end TensorCubeEvaluationPart
