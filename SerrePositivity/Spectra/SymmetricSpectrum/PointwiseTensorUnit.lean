module

public import SerrePositivity.Spectra.SymmetricSequence.FreeZeroUnit
public import SerrePositivity.Spectra.SymmetricSpectrum.PointwiseTensorFunctor
public import SerrePositivity.Spectra.SymmetricSpectrum.FreeMonoidal

/-! # 各段のsmashによる作用の単位比較 -/

@[expose] public section

universe u

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.SymmetricSpectrum

open CategoryTheory CategoryTheory.MonoidalCategory
open SerrePositivity.PointedSimplicialSet

/-- S^0から第0段を自由生成するスペクトルと球面スペクトルの比較。 -/
def freeZeroUnitIso : (freeAt 0).obj (𝟙_ PointedSimplicialSet.{u}) ≅ sphere.{u} :=
  freeFunctor.mapIso (SymmetricSequence.freeZeroUnitIso (C := PointedSimplicialSet.{u})) ≪≫
    freeUnitComparison.symm

/-- 単位比較を値域スペクトルに関する自然同型へまとめる。 -/
def pointwiseTensorUnitNatIso :
    pointwiseTensorFunctor (𝟙_ PointedSimplicialSet.{u}) ≅ 𝟭 SymmetricSpectrum.{u} :=
  (sphereTensorFreeZeroPointwiseNatIso (𝟙_ PointedSimplicialSet.{u})).symm ≪≫
    (curriedTensor SymmetricSpectrum.{u}).mapIso freeZeroUnitIso ≪≫
      leftUnitorNatIso SymmetricSpectrum.{u}

/-- 各段のsmashを持つテンソルの作用の単位比較。 -/
def pointwiseTensorUnitIso (E : SymmetricSpectrum.{u}) :
    pointwiseTensor (𝟙_ PointedSimplicialSet.{u}) E ≅ E := pointwiseTensorUnitNatIso.app E

/-- 単位比較は値域スペクトルの射に関して自然。 -/
@[reassoc]
lemma pointwiseTensorUnitIso_naturality {E F : SymmetricSpectrum.{u}} (f : E ⟶ F) :
    (pointwiseTensorFunctor (𝟙_ PointedSimplicialSet.{u})).map f ≫
        (pointwiseTensorUnitIso F).hom = (pointwiseTensorUnitIso E).hom ≫ f :=
  pointwiseTensorUnitNatIso.hom.naturality f

end SerrePositivity.SymmetricSpectrum
