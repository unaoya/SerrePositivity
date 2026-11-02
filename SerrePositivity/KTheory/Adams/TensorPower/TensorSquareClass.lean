module

public import SerrePositivity.KTheory.Adams.TensorPower.TensorSquareFiltration
public import SerrePositivity.PerfectComplex.Eigen.Involution
public import SerrePositivity.PerfectComplex.ClosedSupport.Cup
public import SerrePositivity.KTheory.Adams.TensorPower.TensorSquare

/-! # 巡回テンソル二乗の類

## 概要

巡回テンソル二乗の類が短完全列で加法的であること、非輪状な複体の類が零であることを示し、台つきホモトピー対象の上のテンソル二乗の評価を与える。

## 方針

フィルトレーションの各層の類を足し、混合成分の打ち消しを使う。

## 規約

`tensorSquareEvaluation*` の名前は残す。

## 使われ方

`Adams/CyclicTwo`。
-/

@[expose] public noncomputable section

universe u

section TensorSquareAdditivityPart

set_option backward.isDefEq.respectTransparency false

namespace SerrePositivity
open CategoryTheory Category Limits
variable {R : Type u} [CommRing R] [Invertible (2 : R)]

namespace Adams

/-- The class of the positive tensor square minus the class of the negative tensor square. -/
def tensorSquareClass (P : CochainComplex (ModuleCat.{u} R) ℤ)
    (Z : TopologicalSpace.Closeds (PrimeSpectrum R))
    (hp : strictlyPerfectComplex R P) (hs : HasHomologySupportOn Z P) : K0WithSupport Z :=
  (tensorSquareInvolution P).k0Class Z (tensorSquare_perfect P hp) (tensorSquare_support hp hs)

lemma tensorSquareClass_shortExact
    (Z : TopologicalSpace.Closeds (PrimeSpectrum R))
    (S : ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ)) (hS : S.ShortExact)
    (ha : strictlyPerfectComplex R S.X₁) (hp : strictlyPerfectComplex R S.X₂)
    (hd : strictlyPerfectComplex R S.X₃)
    (hsA : HasHomologySupportOn Z S.X₁) (hsP : HasHomologySupportOn Z S.X₂)
    (hsD : HasHomologySupportOn Z S.X₃) :
    tensorSquareClass S.X₂ Z hp hsP =
      tensorSquareClass S.X₁ Z ha hsA + tensorSquareClass S.X₃ Z hd hsD := by
  let hproj := fun i => (hd.2 i).2
  have hout := CochainInvolution.k0Class_shortExact Z (tensorSquareKernelShortComplex S.g)
    (tensorSquareKernelInvolution S.g) (tensorSquareInvolution S.X₂) (tensorSquareInvolution S.X₃)
    (tensorSquareKernelSwap_inclusion S.g) (tensorSquareSwap_naturality S.g).symm
    (tensorSquareKernelShortComplex_shortExact S hS hproj)
    (tensorSquareKernel_perfect S hS hp hd) (tensorSquare_perfect S.X₂ hp)
    (tensorSquare_perfect S.X₃ hd) (tensorSquareKernel_support S hS hp hd hsP hsD)
    (tensorSquare_support hp hsP) (tensorSquare_support hd hsD)
  have hin := CochainInvolution.k0Class_shortExact Z (tensorSquareMixedShortComplex S hS hproj)
    (tensorSquareInvolution S.X₁) (tensorSquareKernelInvolution S.g) (tensorSquareMixedInvolution S)
    (tensorSquareKernelFirstMap_swap S).symm (tensorSquareMixedMap_swap S hS hproj)
    (tensorSquareMixedShortComplex_shortExact S hS hproj)
    (tensorSquare_perfect S.X₁ ha) (tensorSquareKernel_perfect S hS hp hd)
    (tensorSquareMixed_perfect S ha hd) (tensorSquare_support ha hsA)
    (tensorSquareKernel_support S hS hp hd hsP hsD) (tensorSquareMixed_support S ha hd hsA hsD)
  dsimp only [tensorSquareKernelShortComplex, tensorSquareMixedShortComplex] at hout hin
  dsimp only [tensorSquareClass]
  rw [hout, hin, tensorSquareMixed_k0Class_eq_zero S Z ha hd hsA hsD, add_zero]

end Adams
end SerrePositivity

end TensorSquareAdditivityPart

section TensorSquareAcyclicClassPart

set_option backward.isDefEq.respectTransparency false

namespace SerrePositivity
open CategoryTheory Category Limits
variable {R : Type u} [CommRing R] [Invertible (2 : R)]

namespace Adams

lemma tensorSquareClass_eq_zero_of_acyclic
    (P : CochainComplex (ModuleCat.{u} R) ℤ) (Z : TopologicalSpace.Closeds (PrimeSpectrum R))
    (hp : strictlyPerfectComplex R P) (hs : HasHomologySupportOn Z P) (hac : P.Acyclic) :
    tensorSquareClass P Z hp hs = 0 := by
  have ht : (tensorSquare P).Acyclic := (cochainAcyclic_iff_support_bot _).mpr
    (tensorSquare_support hp ((cochainAcyclic_iff_support_bot P).mp hac))
  exact (tensorSquareInvolution P).k0Class_eq_zero_of_acyclic Z
    (tensorSquare_perfect P hp) (tensorSquare_support hp hs) ht

end Adams
end SerrePositivity

end TensorSquareAcyclicClassPart

section TensorSquareEvaluationPart

set_option backward.isDefEq.respectTransparency false

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

end TensorSquareEvaluationPart
