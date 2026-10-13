module

public import SerrePositivity.Spectra.SymmetricSequence.TensorPowerMultiplication
public import SerrePositivity.Spectra.SymmetricSequence.SphereSequence

/-! # 球面対称列の convolution 上の乗法

円の反復 smash の連結をconvolutionへ降ろす。
ここでは乗法とその因子化を構成する。可換モノイドの法則はまだ登録しない。
-/

@[expose] public section

universe u

noncomputable section

namespace SerrePositivity.PointedSimplicialSet

open CategoryTheory CategoryTheory.MonoidalCategory

/-- 円の反復 smash の各次数の連結から得る自然変換。 -/
def sphereAppend :
    externalProduct sphereSequence.{u} sphereSequence.{u} ⟶
      FiniteBijection.sumFunctor ⋙ sphereSequence.{u} :=
  SymmetricSequence.tensorPowerAppend (circle : PointedSimplicialSet.{u})

/-- 球面対称列のconvolution上の乗法。 -/
def sphereMultiplication :
    SymmetricSequence.convolution sphereSequence.{u} sphereSequence.{u} ⟶ sphereSequence.{u} :=
  SymmetricSequence.tensorPowerMultiplication (circle : PointedSimplicialSet.{u})

/-- 乗法は、convolutionの標準射との合成によって元の連結を与える。 -/
lemma sphereMultiplication_fac :
    SymmetricSequence.convolutionUnit sphereSequence.{u} sphereSequence.{u} ≫
        Functor.whiskerLeft FiniteBijection.sumFunctor sphereMultiplication.{u} =
      sphereAppend.{u} :=
  SymmetricSequence.tensorPowerMultiplication_fac (circle : PointedSimplicialSet.{u})

/-- 和次数における球面の乗法の因子化は、既存の連結同型に一致する。 -/
lemma sphereMultiplication_fac_app (m n : ℕ) :
    (SymmetricSequence.convolutionUnit sphereSequence.{u} sphereSequence.{u}).app
        (FiniteBijection.of m, FiniteBijection.of n) ≫
        sphereMultiplication.{u}.app (FiniteBijection.of (m + n)) =
      (spherePowerAppendIso.{u} m n).hom :=
  SymmetricSequence.tensorPowerMultiplication_fac_app (circle : PointedSimplicialSet.{u}) m n

end SerrePositivity.PointedSimplicialSet
