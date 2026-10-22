module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovZeroPro

/-!
概要：元の射の j 次群の pro 同型を、j を保持する元の有限切断射の群へ送る。
方針：元の商射の自然性の正方形と、その保持される次数の各段同型を使う。
規約：元の実レベル射を保持。使われ方：底を揃えた源の層射の pro 比較。
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
variable (R : Type u) [CommRing R] {A B : Tower (NonpositiveAlgebra R)} (f : LevelHom A B)

lemma postnikovMap_groups_proIso (n j : ℤ) (hj : j ≤ n)
    (hf : IsProIso ((f.map (nonpositiveInclusion R)).map (groups R j))) :
    IsProIso ((f.map (postnikovFunctor R n)).map (groups R j)) := by
  let a := TowerDiagram.mapNat A (postnikovQuotientNatTrans R n)
  let b := TowerDiagram.mapNat B (postnikovQuotientNatTrans R n)
  have : ∀ i, IsIso ((a.map (groups R j)).app i) :=
    fun i => postnikovQuotient_groups_isIso R (A.obj i).obj n j hj
  have : ∀ i, IsIso ((b.map (groups R j)).app i) :=
    fun i => postnikovQuotient_groups_isIso R (B.obj i).obj n j hj
  apply TowerDiagram.proIso_of_square ((f.map (nonpositiveInclusion R)).map (groups R j))
    ((f.map (postnikovFunctor R n)).map (groups R j)) (a.map (groups R j))
    (b.map (groups R j)) ?_ hf
  apply ProSpectrum.levelHom_ext
  intro i
  change (groups R j).map (f.app i).hom ≫
      (groups R j).map (postnikovQuotient R (B.obj i).obj n) =
    (groups R j).map (postnikovQuotient R (A.obj i).obj n) ≫
      (groups R j).map (postnikovMap R (f.app i).hom n)
  rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
  exact congrArg (groups R j).map (postnikovQuotient_naturality R (f.app i).hom n).symm

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
