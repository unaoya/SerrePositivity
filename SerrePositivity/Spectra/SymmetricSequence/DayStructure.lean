module

public import SerrePositivity.Spectra.SymmetricSequence.Convolution
public import SerrePositivity.Spectra.SymmetricSequence.SumMonoidal
public import Mathlib.CategoryTheory.Monoidal.DayConvolution

/-!
# 具体的な convolution と Day convolution の接続

直和のテンソル関手は既存の直和関手と同じなので、構成した convolution は Day convolution。
単位候補も、空集合からの左 Kan 拡張として構成する。
これらの補助クラスは大域的な instance とせず、モノイダル構造の構成に明示的に渡す。
-/

@[expose] public section

universe v u

noncomputable section

namespace SerrePositivity.SymmetricSequence

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [HasColimitsOfSize.{0, 0} C]

/-- 既存の具体的な convolution が Day convolution であること。 -/
@[instance_reducible]
def dayConvolution (F G : SymmetricSequence C) :
    DayConvolution (toFunctorCategory.obj F) (toFunctorCategory.obj G) where
  convolution := convolution F G
  unit := convolutionUnit F G
  isPointwiseLeftKanExtensionUnit := convolutionIsPointwise F G

/-- 空集合にテンソル単位を置く対称列。空集合の包含に沿う左 Kan 拡張で定義する。 -/
def convolutionTensorUnit : SymmetricSequence C :=
  (Functor.fromPUnit.{0} (FiniteBijection.of 0)).pointwiseLeftKanExtension
    (Functor.fromPUnit.{0} (𝟙_ C))

/-- convolutionの単位対象を定める、空集合からの左Kan拡張の標準射。 -/
def convolutionUnitCan :
    Functor.fromPUnit.{0} (𝟙_ C) ⟶
      Functor.fromPUnit.{0} (FiniteBijection.of 0) ⋙ convolutionTensorUnit :=
  (Functor.fromPUnit.{0} (FiniteBijection.of 0)).pointwiseLeftKanExtensionUnit
    (Functor.fromPUnit.{0} (𝟙_ C))

instance convolutionTensorUnit_isLeftKanExtension :
    (convolutionTensorUnit (C := C)).IsLeftKanExtension (convolutionUnitCan (C := C)) :=
  inferInstanceAs ((Functor.pointwiseLeftKanExtension
    (Functor.fromPUnit.{0} (FiniteBijection.of 0))
    (Functor.fromPUnit.{0} (𝟙_ C))).IsLeftKanExtension
      ((Functor.fromPUnit.{0} (FiniteBijection.of 0)).pointwiseLeftKanExtensionUnit
        (Functor.fromPUnit.{0} (𝟙_ C))))

/-- 単位候補は Day convolution の単位の普遍性を持つ。 -/
@[instance_reducible]
def dayConvolutionUnit : DayConvolutionUnit (toFunctorCategory.obj
    (convolutionTensorUnit (C := C))) where
  can := ((Functor.fromPUnit.{0} (FiniteBijection.of 0)).pointwiseLeftKanExtensionUnit
    (Functor.fromPUnit.{0} (𝟙_ C))).app ⟨⟨⟩⟩
  isPointwiseLeftKanExtensionCan := by
    convert Functor.pointwiseLeftKanExtensionIsPointwiseLeftKanExtension
      (Functor.fromPUnit.{0} (FiniteBijection.of 0)) (Functor.fromPUnit.{0} (𝟙_ C)) using 1
    congr 1

/-- Day 構造を具体的な対称列の型へ誘導するためのデータ。 -/
@[instance_reducible]
def dayCore : InducedLawfulDayConvolutionMonoidalCategoryStructCore
    FiniteBijection C (SymmetricSequence C) where
  ι := toFunctorCategory
  fullyFaithfulι := Functor.FullyFaithful.ofFullyFaithful toFunctorCategory
  tensorObj := convolution
  convolutions' := dayConvolution
  tensorObjIsoConvolution _ _ := Iso.refl _
  tensorUnit := convolutionTensorUnit
  tensorUnitConvolutionUnit := dayConvolutionUnit

end SerrePositivity.SymmetricSequence
