module

public import SerrePositivity.PerfectComplex.ClosedSupport.Cup
public import SerrePositivity.PerfectComplex.Eigen.Involution
public import SerrePositivity.HomologicalAlgebra.CochainTensor.BaseChange
public import SerrePositivity.PerfectComplex.Tensor.Perfect
public import SerrePositivity.HomologicalAlgebra.CochainTensor.Shuffle
public import SerrePositivity.PerfectComplex.Eigen.InvolutionTensor
public import SerrePositivity.PerfectComplex.ClosedSupport.Functoriality
public import SerrePositivity.HomologicalAlgebra.Complex.Idempotent

/-! # テンソル二乗の符号付き巡回作用と固有空間

## 概要

テンソル二乗の符号付きの巡回作用と、正と負の固有空間の複体を定め、固有空間が擬同型を保つこと、テンソルの基底変更が符号付きの対称性・固有空間と両立すること、乗法性のための同変なシャッフルを与える。

## 方針

固有空間は (1 ± τ)/2 の像として HomologicalAlgebra/Complex/Idempotent の像で取る。

## 規約

`tensorSquare`・`tensorSquare{Positive,Negative}*` などの名前は群の外から参照されるので残す。

## 使われ方

`TensorPower/TensorSquareFiltration`・`TensorSquareClass`、`Adams/CyclicTwo`。
-/

@[expose] public noncomputable section

universe u

section TensorSquarePart

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity
open CategoryTheory Category Limits MonoidalCategory HomologicalComplex
variable {R : Type u} [CommRing R]

namespace Adams

/-- The standard total tensor square. -/
abbrev tensorSquare (P : CochainComplex (ModuleCat.{u} R) ℤ) := cochainTensor P P

/-- A chain map induces its tensor square. -/
abbrev tensorSquareMap {P Q : CochainComplex (ModuleCat.{u} R) ℤ} (f : P ⟶ Q) :
    tensorSquare P ⟶ tensorSquare Q := cochainTensorMap f f

/-- The generator of the signed cyclic action of order two. -/
abbrev tensorSquareSwap (P : CochainComplex (ModuleCat.{u} R) ℤ) :
    tensorSquare P ⟶ tensorSquare P := (cochainTensorSymmetry P P).hom

@[simp]
lemma tensorSquareSwap_sq (P : CochainComplex (ModuleCat.{u} R) ℤ) :
    tensorSquareSwap P ≫ tensorSquareSwap P = 𝟙 _ := cochainTensorSymmetry_hom_comp P P

@[reassoc]
lemma tensorSquareSwap_naturality {P Q : CochainComplex (ModuleCat.{u} R) ℤ} (f : P ⟶ Q) :
    tensorSquareMap f ≫ tensorSquareSwap Q = tensorSquareSwap P ≫ tensorSquareMap f :=
  cochainTensorSymmetry_naturality f f

lemma tensorSquare_perfect (P : CochainComplex (ModuleCat.{u} R) ℤ)
    (hp : strictlyPerfectComplex R P) : strictlyPerfectComplex R (tensorSquare P) :=
  strictlyPerfectComplex_cochainTensor P P hp hp

lemma tensorSquare_support {Z : TopologicalSpace.Closeds (PrimeSpectrum R)}
    {P : CochainComplex (ModuleCat.{u} R) ℤ} (hp : strictlyPerfectComplex R P)
    (hs : HasHomologySupportOn Z P) : HasHomologySupportOn Z (tensorSquare P) :=
  hs.cochainTensor_left hp P

/-- The homogeneous formula for the cyclic generator includes the Koszul sign. -/
lemma ιTensorObj_tensorSquareSwap (P : CochainComplex (ModuleCat.{u} R) ℤ)
    (i j n : ℤ) (h : i + j = n) :
    ιTensorObj P P i j n h ≫ (tensorSquareSwap P).f n =
      (i * j).negOnePow • ((β_ (P.X i) (P.X j)).hom ≫
        ιTensorObj P P j i n (by omega)) :=
  ιTensorObj_cochainTensorSymmetry P P i j n h
end Adams
end SerrePositivity

end TensorSquarePart

section TensorSquareEigenspacesPart

set_option backward.isDefEq.respectTransparency false

namespace SerrePositivity
open CategoryTheory Category Limits
variable {R : Type u} [CommRing R]

namespace Adams

/-- The signed tensor-square exchange as an involution. -/
def tensorSquareInvolution (P : CochainComplex (ModuleCat.{u} R) ℤ) :
    CochainInvolution (tensorSquare P) := ⟨tensorSquareSwap P, tensorSquareSwap_sq P⟩

variable [Invertible (2 : R)]

/-- The positive tensor-square projector. -/
abbrev tensorSquarePositiveProjector (P : CochainComplex (ModuleCat.{u} R) ℤ) :=
  (tensorSquareInvolution P).positive

/-- The negative tensor-square projector. -/
abbrev tensorSquareNegativeProjector (P : CochainComplex (ModuleCat.{u} R) ℤ) :=
  (tensorSquareInvolution P).negative

/-- The positive part of the tensor square. -/
abbrev tensorSquarePositive (P : CochainComplex (ModuleCat.{u} R) ℤ) :=
  (tensorSquarePositiveProjector P).image

/-- The negative part of the tensor square. -/
abbrev tensorSquareNegative (P : CochainComplex (ModuleCat.{u} R) ℤ) :=
  (tensorSquareNegativeProjector P).image

lemma tensorSquarePositiveProjector_map (P : CochainComplex (ModuleCat.{u} R) ℤ) :
    (tensorSquarePositiveProjector P).map = (⅟(2 : R)) • (𝟙 _ + tensorSquareSwap P) := rfl

lemma tensorSquareNegativeProjector_map (P : CochainComplex (ModuleCat.{u} R) ℤ) :
    (tensorSquareNegativeProjector P).map = (⅟(2 : R)) • (𝟙 _ - tensorSquareSwap P) :=
  (tensorSquareInvolution P).negative_map

/-- The tensor square splits into its two eigenspaces. -/
def tensorSquareDecompositionIso (P : CochainComplex (ModuleCat.{u} R) ℤ) :
    tensorSquarePositive P ⊞ tensorSquareNegative P ≅ tensorSquare P :=
  (tensorSquareInvolution P).decompositionIso

lemma tensorSquarePositive_perfect (P : CochainComplex (ModuleCat.{u} R) ℤ)
    (hp : strictlyPerfectComplex R P) : strictlyPerfectComplex R (tensorSquarePositive P) :=
  (tensorSquarePositiveProjector P).image_strictlyPerfect (tensorSquare_perfect P hp)

lemma tensorSquareNegative_perfect (P : CochainComplex (ModuleCat.{u} R) ℤ)
    (hp : strictlyPerfectComplex R P) : strictlyPerfectComplex R (tensorSquareNegative P) :=
  (tensorSquareNegativeProjector P).image_strictlyPerfect (tensorSquare_perfect P hp)

lemma tensorSquarePositive_support {Z : TopologicalSpace.Closeds (PrimeSpectrum R)}
    {P : CochainComplex (ModuleCat.{u} R) ℤ} (hp : strictlyPerfectComplex R P)
    (hs : HasHomologySupportOn Z P) : HasHomologySupportOn Z (tensorSquarePositive P) :=
  (tensorSquarePositiveProjector P).image_support (tensorSquare_support hp hs)

lemma tensorSquareNegative_support {Z : TopologicalSpace.Closeds (PrimeSpectrum R)}
    {P : CochainComplex (ModuleCat.{u} R) ℤ} (hp : strictlyPerfectComplex R P)
    (hs : HasHomologySupportOn Z P) : HasHomologySupportOn Z (tensorSquareNegative P) :=
  (tensorSquareNegativeProjector P).image_support (tensorSquare_support hp hs)

@[reassoc]
lemma tensorSquarePositive_inclusion_swap (P : CochainComplex (ModuleCat.{u} R) ℤ) :
    (tensorSquarePositiveProjector P).inclusion ≫ tensorSquareSwap P =
      (tensorSquarePositiveProjector P).inclusion :=
  (tensorSquareInvolution P).positive_inclusion_map

@[reassoc]
lemma tensorSquareNegative_inclusion_swap (P : CochainComplex (ModuleCat.{u} R) ℤ) :
    (tensorSquareNegativeProjector P).inclusion ≫ tensorSquareSwap P =
      -(tensorSquareNegativeProjector P).inclusion :=
  (tensorSquareInvolution P).negative_inclusion_map

end Adams
end SerrePositivity

end TensorSquareEigenspacesPart

section TensorSquareMapsPart

set_option backward.isDefEq.respectTransparency false

namespace SerrePositivity
open CategoryTheory Category Limits
variable {R : Type u} [CommRing R] [Invertible (2 : R)]

namespace Adams
variable {P Q : CochainComplex (ModuleCat.{u} R) ℤ}

abbrev tensorSquarePositiveMap (f : P ⟶ Q) : tensorSquarePositive P ⟶ tensorSquarePositive Q :=
  CochainInvolution.positiveImageMap (tensorSquareInvolution P) (tensorSquareInvolution Q)
    (tensorSquareMap f) (tensorSquareSwap_naturality f).symm

abbrev tensorSquareNegativeMap (f : P ⟶ Q) : tensorSquareNegative P ⟶ tensorSquareNegative Q :=
  CochainInvolution.negativeImageMap (tensorSquareInvolution P) (tensorSquareInvolution Q)
    (tensorSquareMap f) (tensorSquareSwap_naturality f).symm

lemma tensorSquarePositiveMap_quasiIso (f : P ⟶ Q) [QuasiIso f]
    (hp : strictlyPerfectComplex R P) (hq : strictlyPerfectComplex R Q) :
    QuasiIso (tensorSquarePositiveMap f) := by
  have : QuasiIso (tensorSquareMap f) := cochainTensorMap_quasiIso hp hq hp hq f f
  exact CochainInvolution.positiveImageMap_quasiIso _ _ _ _

lemma tensorSquareNegativeMap_quasiIso (f : P ⟶ Q) [QuasiIso f]
    (hp : strictlyPerfectComplex R P) (hq : strictlyPerfectComplex R Q) :
    QuasiIso (tensorSquareNegativeMap f) := by
  have : QuasiIso (tensorSquareMap f) := cochainTensorMap_quasiIso hp hq hp hq f f
  exact CochainInvolution.negativeImageMap_quasiIso _ _ _ _

lemma tensorSquarePositiveMap_homotopyEquivalence (f : P ⟶ Q) [QuasiIso f]
    (hp : strictlyPerfectComplex R P) (hq : strictlyPerfectComplex R Q) :
    HomologicalComplex.homotopyEquivalences (ModuleCat.{u} R) (.up ℤ)
      (tensorSquarePositiveMap f) := by
  have := tensorSquarePositiveMap_quasiIso f hp hq
  exact (strictlyPerfectComplex_quasiIso_iff
    (tensorSquarePositive_perfect P hp) (tensorSquarePositive_perfect Q hq) _).mp inferInstance

lemma tensorSquareNegativeMap_homotopyEquivalence (f : P ⟶ Q) [QuasiIso f]
    (hp : strictlyPerfectComplex R P) (hq : strictlyPerfectComplex R Q) :
    HomologicalComplex.homotopyEquivalences (ModuleCat.{u} R) (.up ℤ)
      (tensorSquareNegativeMap f) := by
  have := tensorSquareNegativeMap_quasiIso f hp hq
  exact (strictlyPerfectComplex_quasiIso_iff
    (tensorSquareNegative_perfect P hp) (tensorSquareNegative_perfect Q hq) _).mp inferInstance

end Adams
end SerrePositivity

end TensorSquareMapsPart

section TensorSquareBaseChangePart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity
open CategoryTheory Category Limits MonoidalCategory HomologicalComplex
open Functor.OplaxMonoidal
variable {R S : Type u} [CommRing R] [CommRing S]

namespace Adams

/-- Base change of the tensor square intertwines its signed involution. -/
@[reassoc]
lemma tensorSquareBaseChangeIso_swap (φ : R →+* S)
    (P : CochainComplex (ModuleCat.{u} R) ℤ) :
    ((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).map
        (tensorSquareSwap P) ≫ (cochainTensorBaseChangeIso φ P P).hom =
      (cochainTensorBaseChangeIso φ P P).hom ≫ tensorSquareSwap (baseChange φ P) :=
  cochainTensorBaseChangeIso_symmetry φ P P

end Adams

end SerrePositivity

end TensorSquareBaseChangePart

section TensorSquareBaseChangeEigenspacesPart

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity
open CategoryTheory Category Limits
variable {R S : Type u} [CommRing R] [CommRing S]
variable [Invertible (2 : R)] [Invertible (2 : S)]
namespace Adams
variable (φ : R →+* S) (P : CochainComplex (ModuleCat.{u} R) ℤ)

def tensorSquarePositiveBaseChangeIso :
    baseChange φ (tensorSquarePositive P) ≅ tensorSquarePositive (baseChange φ P) :=
  CochainInvolution.positiveBaseChangeIso φ (tensorSquareInvolution P) ≪≫
    CochainIdempotent.imageIso _ _ (cochainTensorBaseChangeIso φ P P)
      (CochainInvolution.positive_naturality _ _ _ (tensorSquareBaseChangeIso_swap φ P))

def tensorSquareNegativeBaseChangeIso :
    baseChange φ (tensorSquareNegative P) ≅ tensorSquareNegative (baseChange φ P) :=
  CochainInvolution.negativeBaseChangeIso φ (tensorSquareInvolution P) ≪≫
    CochainIdempotent.imageIso _ _ (cochainTensorBaseChangeIso φ P P)
      (CochainInvolution.negative_naturality _ _ _ (tensorSquareBaseChangeIso_swap φ P))

@[reassoc]
lemma tensorSquarePositiveBaseChangeIso_hom_inclusion :
    (tensorSquarePositiveBaseChangeIso φ P).hom ≫
        (tensorSquarePositiveProjector (baseChange φ P)).inclusion =
      ((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).map
          (tensorSquarePositiveProjector P).inclusion ≫
        (cochainTensorBaseChangeIso φ P P).hom := by
  simp only [tensorSquarePositiveBaseChangeIso, Iso.trans_hom, Category.assoc,
    CochainIdempotent.imageIso_hom_inclusion,
    CochainInvolution.positiveBaseChangeIso_hom_inclusion_assoc]

@[reassoc]
lemma tensorSquareNegativeBaseChangeIso_hom_inclusion :
    (tensorSquareNegativeBaseChangeIso φ P).hom ≫
        (tensorSquareNegativeProjector (baseChange φ P)).inclusion =
      ((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).map
          (tensorSquareNegativeProjector P).inclusion ≫
        (cochainTensorBaseChangeIso φ P P).hom := by
  simp only [tensorSquareNegativeBaseChangeIso, Iso.trans_hom, Category.assoc,
    CochainIdempotent.imageIso_hom_inclusion,
    CochainInvolution.negativeBaseChangeIso_hom_inclusion_assoc]

end Adams
end SerrePositivity

end TensorSquareBaseChangeEigenspacesPart

section TensorSquareShufflePart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity
open CategoryTheory Category Limits HomologicalComplex
variable {R : Type u} [CommRing R]
namespace Adams

def tensorSquareTensorIso (P Q : CochainComplex (ModuleCat.{u} R) ℤ) :
    tensorSquare (cochainTensor P Q) ≅ cochainTensor (tensorSquare P) (tensorSquare Q) :=
  cochainTensorShuffle P Q P Q

abbrev tensorSquareDiagonalSwap (P Q : CochainComplex (ModuleCat.{u} R) ℤ) :=
  cochainTensorMap (tensorSquareSwap P) (tensorSquareSwap Q)

/-- The signed shuffle identifies block exchange with the tensor of the two square exchanges. -/
lemma tensorSquareTensorIso_swap (P Q : CochainComplex (ModuleCat.{u} R) ℤ) :
    tensorSquareSwap (cochainTensor P Q) ≫ (tensorSquareTensorIso P Q).hom =
      (tensorSquareTensorIso P Q).hom ≫ tensorSquareDiagonalSwap P Q :=
  cochainTensorShuffle_symmetry P Q P Q

variable [Invertible (2 : R)]

def tensorSquareTensorPositiveIso (P Q : CochainComplex (ModuleCat.{u} R) ℤ) :
    tensorSquarePositive (cochainTensor P Q) ≅
      ((tensorSquareInvolution P).tensor (tensorSquareInvolution Q)).positive.image :=
  CochainIdempotent.imageIso (tensorSquarePositiveProjector (cochainTensor P Q))
    (((tensorSquareInvolution P).tensor (tensorSquareInvolution Q)).positive)
    (tensorSquareTensorIso P Q)
    (CochainInvolution.positive_naturality _ _ _ (tensorSquareTensorIso_swap P Q))

def tensorSquareTensorNegativeIso (P Q : CochainComplex (ModuleCat.{u} R) ℤ) :
    tensorSquareNegative (cochainTensor P Q) ≅
      ((tensorSquareInvolution P).tensor (tensorSquareInvolution Q)).negative.image :=
  CochainIdempotent.imageIso (tensorSquareNegativeProjector (cochainTensor P Q))
    (((tensorSquareInvolution P).tensor (tensorSquareInvolution Q)).negative)
    (tensorSquareTensorIso P Q)
    (CochainInvolution.negative_naturality _ _ _ (tensorSquareTensorIso_swap P Q))

end Adams
end SerrePositivity

end TensorSquareShufflePart
