module

public import SerrePositivity.Spectra.SymmetricSpectrum.Basic

/-! # 球面スペクトル

概要：円周のテンソル冪でできる対称列の正則加群を球面スペクトルに取る。
方針：一般の `GeneralSymmetricSpectrum` を円周に特殊化し、`Mod.regular` と球面列の乗法を使う。
規約：構造射の和次数は `GeneralSymmetricSpectrum.structureMap` の規約に従う。
使われ方：自由円周スペクトルとテンソル積の比較。
-/

@[expose] public section

universe u

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.SymmetricSpectrum

open CategoryTheory CategoryTheory.MonoidalCategory
open GeneralSymmetricSpectrum (action structureMap underlying)
open PointedSimplicialSet

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
