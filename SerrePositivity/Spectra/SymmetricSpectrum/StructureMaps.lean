module

public import SerrePositivity.Spectra.General.StructureMaps
public import SerrePositivity.Spectra.SymmetricSpectrum.Basic

/-! # 円周スペクトルの構造射と置換作用

一般の構造射の同変性を、反復 smash に対する球面の置換作用で表す。
-/

@[expose] public section

universe u

noncomputable section

open CategoryTheory CategoryTheory.MonoidalCategory

namespace SerrePositivity.SymmetricSpectrum

open GeneralSymmetricSpectrum (structureMap)

open SerrePositivity.PointedSimplicialSet

/-- 各次数の構造射は左右ブロックの置換と両立する。 -/
lemma structureMap_equivariance (E : SymmetricSpectrum.{u}) (p q : ℕ)
    (σ : Equiv.Perm (Fin p)) (τ : Equiv.Perm (Fin q)) :
    PointedObject.smashMap (spherePermutationAction.{u} p σ).asIso.hom
        (E.X.map (FiniteBijection.permutation q τ)) ≫ structureMap E p q =
      structureMap E p q ≫ E.X.map
        (FiniteBijection.sumMap (FiniteBijection.permutation p σ)
          (FiniteBijection.permutation q τ)) := by
  rw [← sphereSequence_map_permutation]
  exact GeneralSymmetricSpectrum.structureMap_equivariance E p q σ τ

end SerrePositivity.SymmetricSpectrum
