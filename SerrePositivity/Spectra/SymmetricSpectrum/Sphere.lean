module

public import SerrePositivity.Spectra.SymmetricSpectrum.StructureMaps

/-! # 球面スペクトル

既存の球面モノイドを自身上の正則加群として対称スペクトルにし、作用と構造射を比較する。
-/

@[expose] public section

universe u

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.MonoidalCategory

namespace SerrePositivity.SymmetricSpectrum

open GeneralSymmetricSpectrum (action structureMap underlying)

open SerrePositivity.PointedSimplicialSet

/-- 球面モノイドの正則加群としての球面スペクトル。 -/
def sphere : SymmetricSpectrum.{u} := Mod.regular sphereSequence.{u}
/-- 球面スペクトルの underlying 対称列は既存の球面対称列。 -/
lemma sphere_underlying : underlying sphere.{u} = sphereSequence.{u} := rfl
/-- 球面スペクトルの作用は球面モノイドの乗法。 -/
lemma sphere_action : action sphere.{u} = sphereMultiplication.{u} := rfl
/-- 球面スペクトルの構造射は既存の円の反復smashの連結同型。 -/
lemma sphere_structureMap (p q : ℕ) :
    structureMap sphere.{u} p q = (spherePowerAppendIso.{u} p q).hom :=
  sphereMultiplication_fac_app p q


end SerrePositivity.SymmetricSpectrum
