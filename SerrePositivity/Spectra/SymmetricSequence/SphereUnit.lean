module

public import SerrePositivity.Spectra.SymmetricSequence.TensorPowerUnitLaws
public import SerrePositivity.Spectra.SymmetricSequence.SphereMultiplication

/-! # 球面対称列への単位射

第0段の恒等射を、空集合からの左Kan拡張の普遍性で単位射へ延長する。
convolution全体の左右単位則も含む。結合則とモノイド構造の登録はまだ含まない。
-/

@[expose] public section

universe u

noncomputable section

namespace SerrePositivity.PointedSimplicialSet

open CategoryTheory CategoryTheory.MonoidalCategory

/-- 左Kan拡張で構成した単位対象から球面対称列への単位射。 -/
def sphereUnit :
    SymmetricSequence.convolutionTensorUnit (C := PointedSimplicialSet.{u}) ⟶
      sphereSequence.{u} :=
  SymmetricSequence.tensorPowerUnit (circle : PointedSimplicialSet.{u})

/-- 登録済みのモノイダル単位から球面対称列への単位射。 -/
def sphereUnitHom : 𝟙_ PointedSymmetricSequence.{u} ⟶ sphereSequence.{u} :=
  SymmetricSequence.tensorPowerUnitHom (circle : PointedSimplicialSet.{u})

/-- 二つの表示の単位射は同じ射。 -/
lemma sphereUnitHom_eq : sphereUnitHom.{u} = sphereUnit.{u} := rfl

/-- 単位対象の標準射と球面の単位射の第0段の成分との合成は恒等射。 -/
lemma sphereUnit_fac_app :
    (SymmetricSequence.convolutionUnitCan (C := PointedSimplicialSet.{u})).app ⟨⟨⟩⟩ ≫
        sphereUnit.{u}.app (FiniteBijection.of 0) = 𝟙 (𝟙_ PointedSimplicialSet.{u}) :=
  SymmetricSequence.tensorPowerUnit_fac_app (circle : PointedSimplicialSet.{u})

/-- 球面対称列のconvolution全体の左単位則。 -/
lemma sphere_left_unit :
    (sphereUnitHom.{u} ▷ sphereSequence.{u}) ≫ sphereMultiplication.{u} =
      (λ_ sphereSequence.{u}).hom :=
  SymmetricSequence.tensorPower_left_unit (circle : PointedSimplicialSet.{u})

/-- 球面対称列のconvolution全体の右単位則。 -/
lemma sphere_right_unit :
    (sphereSequence.{u} ◁ sphereUnitHom.{u}) ≫ sphereMultiplication.{u} =
      (ρ_ sphereSequence.{u}).hom :=
  SymmetricSequence.tensorPower_right_unit (circle : PointedSimplicialSet.{u})

end SerrePositivity.PointedSimplicialSet
