module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraDerivationTargetProInverse
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovZeroMapIso
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovImageTargetConnectivity

/-!
概要：n=1 の元の源射の class 図式に、層と平方零標的の実 pro 逆を供給する。
方針：元の π₁ の比較を厳密集中層へ反映し、零底の実同型と二座標を合成する。
規約：class 図式全体の局所化後の逆は次工程。使われ方：源側の実逆 roof。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory HomologicalComplex
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
open ProExcision
variable (R : Type u) [CommRing R] {A B : Tower (NonpositiveAlgebra R)} (f : LevelHom A B)

lemma postnikovNormalizedLayerMap_isProIso
    (hf : IsProIso ((f.map (nonpositiveInclusion R)).map (groups R 1))) :
    IsProIso ((postnikovStrictZeroBaseNonpositiveLift R f 1 (by omega)).map
      (postnikovLayerFunctor R 0)) :=
  postnikovLayerMap_isProIso R 0 _
    (postnikovStrictZeroBaseLift_groups_proIso R f 1 (by omega) 1 (by omega) le_rfl hf)

lemma postnikovNormalizedDerivationTargetMap_isProIso
    (hf : IsProIso ((f.map (nonpositiveInclusion R)).map (groups R 1))) :
    IsProIso ((postnikovStrictZeroBaseNonpositiveLift R f 1 (by omega)).map
      (postnikovDerivationTargetFunctor R 0 (by omega))) := by
  apply postnikovDerivationTargetMap_isProIso R 0 (by omega) _
  · have : ∀ i, IsIso (((postnikovStrictZeroBaseNonpositiveLift R f 1 (by omega)).map
        (postnikovFunctor R 0)).app i) :=
      postnikovStrictZeroBaseLift_zeroMap_isIso R f 1 (by omega)
    exact TowerDiagram.isProIso_of_levelwiseIso _
  · exact postnikovStrictZeroBaseLift_groups_proIso R f 1 (by omega) 1 (by omega) le_rfl hf

lemma postnikovNormalizedPerturbedMap_quasiIso (i : ℕ) :
    QuasiIso (postnikovPerturbedMap R
      ((postnikovStrictZeroBaseNonpositiveLift R f 1 (by omega)).app i).hom 0 (by omega)).hom := by
  have := postnikovStrictZeroBaseLift_zeroMap_isIso R f 1 (by omega) i
  apply postnikovPerturbedMap_quasiIso R _ 0 (by omega)
  exact quasiIso_of_isIso _

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
