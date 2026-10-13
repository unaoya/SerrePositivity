module

public import SerrePositivity.Spectra.SymmetricSequence.DayStructure
public import Mathlib.CategoryTheory.Monoidal.Closed.Braided

/-!
# 対称列の convolution のモノイダル構造

具体的な convolution の Day 構造から結合子と単位を構成する。
基礎圏の閉構造と braiding から左右テンソルの余極限保存を供給し、
Mathlib の一般論によって自然性・pentagon・triangle を得る。
convolution の braiding と閉構造の登録は別に行う。
-/

@[expose] public section

universe v u

noncomputable section

namespace SerrePositivity.SymmetricSequence

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [BraidedCategory C] [MonoidalClosed C] [HasColimitsOfSize.{0, 0} C]

instance convolutionMonoidalCategoryStruct : MonoidalCategoryStruct (SymmetricSequence C) :=
  letI := dayCore (C := C)
  InducedLawfulDayConvolutionMonoidalCategoryStructCore.mkMonoidalCategoryStruct
    FiniteBijection C (SymmetricSequence C)

instance convolutionLawfulDayStructure : LawfulDayConvolutionMonoidalCategoryStruct
    FiniteBijection C (SymmetricSequence C) :=
  letI := dayCore (C := C)
  InducedLawfulDayConvolutionMonoidalCategoryStructCore.mkLawfulDayConvolutionMonoidalCategoryStruct
    FiniteBijection C (SymmetricSequence C)

instance convolutionMonoidalCategory : MonoidalCategory (SymmetricSequence C) :=
  monoidalOfLawfulDayConvolutionMonoidalCategoryStruct
    FiniteBijection C (SymmetricSequence C)

/-- 登録したテンソル積は、既存の具体的な convolution。 -/
lemma tensorObj_eq_convolution (F G : SymmetricSequence C) :
    F ⊗ G = convolution F G := rfl

/-- 登録した単位は空集合からの左 Kan 拡張。 -/
lemma tensorUnit_eq_convolutionTensorUnit :
    𝟙_ (SymmetricSequence C) = convolutionTensorUnit := rfl

end SerrePositivity.SymmetricSequence
