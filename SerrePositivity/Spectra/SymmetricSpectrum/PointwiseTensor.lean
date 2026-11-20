module

public import SerrePositivity.Spectra.SymmetricSequence.PointwiseTensorModule
public import SerrePositivity.Spectra.SymmetricSpectrum.TensorFreeZeroLevels

/-! # 各段が通常のsmashとなるテンソル・スペクトルとF_0との全体の比較 -/

@[expose] public section

universe u

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.SymmetricSpectrum

open GeneralSymmetricSpectrum (level)

open CategoryTheory CategoryTheory.MonoidalCategory
open SerrePositivity.PointedSimplicialSet

/-- 各段がXとEの同じ段の通常のsmashとなる対称スペクトル。 -/
def pointwiseTensor (X : PointedSimplicialSet.{u}) (E : SymmetricSpectrum.{u}) :
    SymmetricSpectrum.{u} := SymmetricSequence.pointwiseTensorModule sphereSequence.{u} X E

/-- 各段のsmashを持つテンソルの値域スペクトルに関する関手。 -/
def pointwiseTensorFunctor (X : PointedSimplicialSet.{u}) :
    SymmetricSpectrum.{u} ⥤ SymmetricSpectrum.{u} :=
  SymmetricSequence.pointwiseTensorModuleFunctor sphereSequence.{u} X

/-- 第q段は通常のsmash。 -/
lemma pointwiseTensor_level (X : PointedSimplicialSet.{u}) (E : SymmetricSpectrum.{u}) (q : ℕ) :
    level (pointwiseTensor X E) q = X ⊗ level E q := rfl

/-- 各段の置換は第二因子の置換との通常のsmash。 -/
lemma pointwiseTensor_permutation (X : PointedSimplicialSet.{u})
    (E : SymmetricSpectrum.{u}) (q : ℕ) (σ : Equiv.Perm (Fin q)) :
    (pointwiseTensor X E).X.map (FiniteBijection.permutation q σ) =
      X ◁ E.X.map (FiniteBijection.permutation q σ) := rfl

/-- F_0 Xとの球面上のテンソル積と各段の通常のsmashを持つスペクトルの全体の比較。 -/
def sphereTensorFreeZeroPointwiseIso (X : PointedSimplicialSet.{u})
    (E : SymmetricSpectrum.{u}) :
    sphereTensor ((freeAt 0).obj X) E ≅ pointwiseTensor X E :=
  SymmetricSequence.freeZeroTensorPointwiseModuleIso sphereSequence.{u} X E

/-- F_0 Xとの全体の比較は値域スペクトルに関する自然同型。 -/
def sphereTensorFreeZeroPointwiseNatIso (X : PointedSimplicialSet.{u}) :
    tensorLeft ((freeAt 0).obj X) ≅ pointwiseTensorFunctor X :=
  SymmetricSequence.freeZeroTensorPointwiseModuleNatIso sphereSequence.{u} X

/-- 自然比較の各成分は構成済みのスペクトル全体の比較。 -/
lemma sphereTensorFreeZeroPointwiseNatIso_app (X : PointedSimplicialSet.{u})
    (E : SymmetricSpectrum.{u}) :
    (sphereTensorFreeZeroPointwiseNatIso X).app E = sphereTensorFreeZeroPointwiseIso X E := rfl

/-- 全体の比較を各段に評価すると、既存の各段のsmashとの比較になる。 -/
lemma sphereTensorFreeZeroPointwiseIso_level (X : PointedSimplicialSet.{u})
    (E : SymmetricSpectrum.{u}) (q : ℕ) :
    (evaluation q).mapIso (sphereTensorFreeZeroPointwiseIso X E) =
      sphereTensorFreeZeroLevelIso X E q :=
  SymmetricSequence.freeZeroTensorPointwiseModuleIso_level sphereSequence.{u} X E q

/-- 関手の各段の射は第二因子の射との通常のsmash。 -/
def pointwiseTensorMapLevelLaw (X : PointedSimplicialSet.{u})
    {E F : SymmetricSpectrum.{u}} (g : E ⟶ F) (q : ℕ) :
    Prop :=
  SymmetricSequence.pointwiseTensorMapLevelLaw sphereSequence.{u} X g
    ((pointwiseTensorFunctor X).map g).hom q

/-- 各段のテンソルの射は通常のsmashの法則を満たす。 -/
lemma pointwiseTensorFunctor_map_app (X : PointedSimplicialSet.{u})
    {E F : SymmetricSpectrum.{u}} (g : E ⟶ F) (q : ℕ) :
    pointwiseTensorMapLevelLaw X g q :=
  SymmetricSequence.pointwiseTensorModuleFunctor_map_levelLaw sphereSequence.{u} X g q

end SerrePositivity.SymmetricSpectrum
