module

public import SerrePositivity.CategoryTheory.Monoidal.TensorPower.FinBijection
public import SerrePositivity.Spectra.SymmetricSequence.TensorPowerSequence
public import SerrePositivity.Spectra.SymmetricSequence.Convolution

/-! # 反復テンソルの対称列の乗法

全単射圏上の連結をconvolutionへ降ろし、因子化と一意性を証明する。
モノイドの結合・単位・可換性の法則は、このモジュールではまだ登録しない。
-/

@[expose] public section

universe v u

noncomputable section

namespace SerrePositivity.SymmetricSequence

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
    [HasColimitsOfSize.{0, 0} C]

/-- 各次数の連結を、対称列の外部テンソル積からの自然変換として読む。 -/
def tensorPowerAppend (X : C) :
    externalProduct (tensorPowerSequence X) (tensorPowerSequence X) ⟶
      FiniteBijection.sumFunctor ⋙ tensorPowerSequence X := TensorPowers.appendNatTrans X

/-- 連結を左Kan拡張の普遍性で降ろした、対称列のconvolution上の乗法。 -/
def tensorPowerMultiplication (X : C) :
    convolution (tensorPowerSequence X) (tensorPowerSequence X) ⟶ tensorPowerSequence X :=
  (convolutionHomEquiv (tensorPowerSequence X) (tensorPowerSequence X)
    (tensorPowerSequence X)).symm (tensorPowerAppend X)

/-- 乗法は、convolutionの標準射との合成によって元の連結を与える。 -/
lemma tensorPowerMultiplication_fac (X : C) :
    convolutionUnit (tensorPowerSequence X) (tensorPowerSequence X) ≫
        Functor.whiskerLeft FiniteBijection.sumFunctor (tensorPowerMultiplication X) =
      tensorPowerAppend X :=
  (convolutionHomEquiv (tensorPowerSequence X) (tensorPowerSequence X)
    (tensorPowerSequence X)).apply_symm_apply (tensorPowerAppend X)

/-- 乗法の各次数の因子化は、既存の連結同型に一致する。 -/
lemma tensorPowerMultiplication_fac_app (X : C) (m n : ℕ) :
    (convolutionUnit (tensorPowerSequence X) (tensorPowerSequence X)).app
        (FiniteBijection.of m, FiniteBijection.of n) ≫
        (tensorPowerMultiplication X).app (FiniteBijection.of (m + n)) =
      (TensorPowers.appendIso X m n).hom :=
  congrArg (fun f ↦ f.app (FiniteBijection.of m, FiniteBijection.of n))
    (tensorPowerMultiplication_fac X)

/-- 元の連結を与えるconvolution上の射は一意である。 -/
lemma tensorPowerMultiplication_unique (X : C)
    (μ : convolution (tensorPowerSequence X) (tensorPowerSequence X) ⟶ tensorPowerSequence X)
    (h : convolutionUnit (tensorPowerSequence X) (tensorPowerSequence X) ≫
        Functor.whiskerLeft FiniteBijection.sumFunctor μ = tensorPowerAppend X) :
    μ = tensorPowerMultiplication X := by
  apply (convolutionHomEquiv (tensorPowerSequence X) (tensorPowerSequence X)
    (tensorPowerSequence X)).injective
  exact h.trans (tensorPowerMultiplication_fac X).symm

end SerrePositivity.SymmetricSequence
