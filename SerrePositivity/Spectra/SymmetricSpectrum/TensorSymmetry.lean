module

public import SerrePositivity.CategoryTheory.Monoidal.BalancedTensorSymmetry
public import SerrePositivity.Spectra.SymmetricSpectrum.TensorLeftUnit

/-! # 球面上のテンソル積の交換同型

基礎対称列のbraidingを釣り合い商へ降ろし、球面作用との両立と自然性を得る。
-/

@[expose] public section

universe u

noncomputable section

namespace SerrePositivity.SymmetricSpectrum

open CategoryTheory CategoryTheory.MonoidalCategory
open SerrePositivity.PointedSimplicialSet

/-- 球面上のテンソル積の二つのスペクトルを交換する同型。 -/
def sphereTensorSymmetry (E F : SymmetricSpectrum.{u}) : sphereTensor E F ≅ sphereTensor F E :=
  MonoidalBalancedTensor.swapIso sphereSequence.{u} E F

/-- スペクトルの交換同型は標準射上で基礎対称列の交換射に一致する。 -/
@[reassoc] lemma tensorProjection_symmetry (E F : SymmetricSpectrum.{u}) :
    tensorProjection E F ≫ (sphereTensorSymmetry E F).hom.hom =
      (β_ E.X F.X).hom ≫ tensorProjection F E :=
  MonoidalBalancedTensor.projection_swapHom sphereSequence.{u} E F

/-- スペクトルの交換同型の逆射は反対順の交換射。 -/
lemma sphereTensorSymmetry_inv (E F : SymmetricSpectrum.{u}) :
    (sphereTensorSymmetry E F).inv = (sphereTensorSymmetry F E).hom := rfl

/-- 球面上のテンソル積の交換は両方のスペクトルの射に関して自然。 -/
lemma sphereTensorSymmetry_naturality {E E' F F' : SymmetricSpectrum.{u}}
    (f : E ⟶ E') (g : F ⟶ F') :
    sphereTensorMap f g ≫ (sphereTensorSymmetry E' F').hom =
      (sphereTensorSymmetry E F).hom ≫ sphereTensorMap g f :=
  MonoidalBalancedTensor.swap_naturality sphereSequence.{u} f g

/-- 球面上のテンソル積を二回交換すると恒等射になる。 -/
lemma sphereTensorSymmetry_symmetry (E F : SymmetricSpectrum.{u}) :
    (sphereTensorSymmetry E F).hom ≫ (sphereTensorSymmetry F E).hom = 𝟙 (sphereTensor E F) :=
  MonoidalBalancedTensor.swapIso_symmetry sphereSequence.{u} E F

/-- 球面上のテンソル積の二変数関手と、入力を交換した関手との自然同型。 -/
def sphereTensorSymmetryNatIso : sphereTensorBifunctor.{u} ≅
    CategoryTheory.Prod.swap SymmetricSpectrum.{u} SymmetricSpectrum.{u} ⋙
      sphereTensorBifunctor.{u} :=
  MonoidalBalancedTensor.swapNatIso sphereSequence.{u}

/-- 球面との交換を左単位比較へ続けると右単位比較になる。 -/
lemma sphereTensorSymmetry_rightUnit (E : SymmetricSpectrum.{u}) :
    sphereTensorSymmetry E sphere ≪≫ sphereTensorLeftUnit E = sphereTensorRightUnit E :=
  MonoidalBalancedTensor.swapIso_rightUnit sphereSequence.{u} E

end SerrePositivity.SymmetricSpectrum
