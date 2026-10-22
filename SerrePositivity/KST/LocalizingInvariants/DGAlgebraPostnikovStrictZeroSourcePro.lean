module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovStrictZeroHomology
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovMapProGroups

/-!
概要：元の正次数群の pro 同型から、底を揃えた元の源射の層群の pro 同型を得る。
方針：元の厳密な因子分解と右射影の各段同型を、元の切断比較の正方形へ接続する。
規約：源射の実代数 pro 逆とは区別する。使われ方：n=1 の源側の逆 roof。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
open ProExcision
variable (R : Type u) [CommRing R] {A B : Tower (NonpositiveAlgebra R)}
  (f : LevelHom A B) (n : ℤ) (hn : 0 ≤ n)

lemma postnikovStrictZeroBaseLift_groups_fac (j : ℤ) :
    ((postnikovStrictZeroBaseLift R f n hn).map (groups R j)).comp
      ((postnikovStrictZeroBaseProjection R f n hn).map (groups R j)) =
        (f.map (postnikovFunctor R n)).map (groups R j) := by
  rw [← TowerDiagram.levelHom_map_comp, postnikovStrictZeroBase_fac]

lemma postnikovStrictZeroBaseLift_groups_proIso (j : ℤ) (hj : 0 < j) (hjn : j ≤ n)
    (hf : IsProIso ((f.map (nonpositiveInclusion R)).map (groups R j))) :
    IsProIso ((postnikovStrictZeroBaseLift R f n hn).map (groups R j)) := by
  have : ∀ i, IsIso (((postnikovStrictZeroBaseProjection R f n hn).map (groups R j)).app i) :=
    postnikovStrictZeroBaseProjection_groups_isIso R f n hn j hj
  apply TowerDiagram.proIso_of_comp_right_levelwiseIso
    ((postnikovStrictZeroBaseProjection R f n hn).map (groups R j))
    ((postnikovStrictZeroBaseLift R f n hn).map (groups R j))
  rw [postnikovStrictZeroBaseLift_groups_fac]
  exact postnikovMap_groups_proIso R f n j hjn hf

/-- 二つの元の商射を通して、源の層射を元の射そのものへ比較する正方形。 -/
lemma postnikovStrictZeroBaseLift_groups_original_square (j : ℤ) :
    ((f.map (nonpositiveInclusion R)).map (groups R j)).comp
      ((TowerDiagram.mapNat B (postnikovQuotientNatTrans R n)).map (groups R j)) =
    ((TowerDiagram.mapNat A (postnikovQuotientNatTrans R n)).map (groups R j)).comp
      (((postnikovStrictZeroBaseLift R f n hn).map (groups R j)).comp
        ((postnikovStrictZeroBaseProjection R f n hn).map (groups R j))) := by
  rw [postnikovStrictZeroBaseLift_groups_fac]
  apply ProSpectrum.levelHom_ext
  intro i
  change (groups R j).map (f.app i).hom ≫
      (groups R j).map (postnikovQuotient R (B.obj i).obj n) =
    (groups R j).map (postnikovQuotient R (A.obj i).obj n) ≫
      (groups R j).map (postnikovMap R (f.app i).hom n)
  rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
  exact congrArg (groups R j).map (postnikovQuotient_naturality R (f.app i).hom n).symm

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
