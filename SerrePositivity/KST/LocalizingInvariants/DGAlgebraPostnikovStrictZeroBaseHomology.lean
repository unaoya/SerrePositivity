module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovStrictZeroHomology

/-!
概要：底を揃えた元の源射は、元の零次数ホモロジーで各段同型になる。
方針：右脚の零次数準同型性から通常模型の左射影を比較し、元の遷移の合成式を使う。
規約：元の射に π₀ の仮定は不要。使われ方：源側の全整数 π-pro 判定。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits HomologicalComplex
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
open ProExcision
variable (R : Type u) [CommRing R] {A B : Tower (NonpositiveAlgebra R)}
  (f : LevelHom A B) (n : ℤ) (hn : 0 ≤ n)

def postnikovStrictZeroBaseLeft :
    LevelHom (postnikovStrictZeroBaseTower R f n hn) (A.map (postnikovFunctor R 0)) :=
  MonoidPullback.leftProjection _ _

lemma postnikovStrictZeroBaseLift_left :
    (postnikovStrictZeroBaseLift R f n hn).comp (postnikovStrictZeroBaseLeft R f n hn) =
      postnikovTransitionLevelHom R A n 0 hn := MonoidPullback.squareLift_comp_left _ _ _ _ _

lemma postnikovStrictZeroBaseLeft_quasiIsoAt_zero (i : ℕ) :
    QuasiIsoAt ((postnikovStrictZeroBaseLeft R f n hn).app i).hom 0 := by
  have hB : (postnikov R (B.obj i).obj 0).X.IsStrictlyGE 0 := by
    change ((postnikovComplex R 0).obj (B.obj i).obj).IsStrictlyGE 0
    simpa only [neg_zero] using postnikovComplex_lowerBound R (B.obj i).obj 0
  let g := (postnikovTransition R (B.obj i).obj n 0 hn).hom
  have hp : Epi (homologyMap g (0 - 1)) :=
    ((postnikov R (B.obj i).obj 0).X.isZero_of_isGE 0 (0 - 1) (by omega)).epi _
  have hi : IsIso (homologyMap g 0) := by
    have := postnikovTransition_quasiIsoAt R (B.obj i).obj n 0 hn 0 (by omega)
    infer_instance
  have hj : Mono (homologyMap g (0 + 1)) := by
    have := postnikovTransition_quasiIsoAt R (B.obj i).obj n 0 hn (0 + 1) (by omega)
    infer_instance
  exact cochainPullback_fst_quasiIsoAt _ g 0 hp hi hj

lemma postnikovStrictZeroBaseLift_quasiIsoAt_zero (i : ℕ) :
    QuasiIsoAt ((postnikovStrictZeroBaseLift R f n hn).app i).hom 0 := by
  have := postnikovStrictZeroBaseLeft_quasiIsoAt_zero R f n hn i
  have he := congrArg (fun s => s.app i) (postnikovStrictZeroBaseLift_left R f n hn)
  have : QuasiIsoAt (((postnikovStrictZeroBaseLift R f n hn).app i).hom ≫
      ((postnikovStrictZeroBaseLeft R f n hn).app i).hom) 0 := by
    change QuasiIsoAt (((postnikovStrictZeroBaseLift R f n hn).app i ≫
      (postnikovStrictZeroBaseLeft R f n hn).app i).hom) 0
    change (postnikovStrictZeroBaseLift R f n hn).app i ≫
      (postnikovStrictZeroBaseLeft R f n hn).app i = _ at he
    rw [he]
    exact postnikovTransition_quasiIsoAt R (A.obj i).obj n 0 hn 0 (by omega)
  exact quasiIsoAt_of_comp_right ((postnikovStrictZeroBaseLift R f n hn).app i).hom
    ((postnikovStrictZeroBaseLeft R f n hn).app i).hom 0

lemma postnikovStrictZeroBaseLift_groups_zero_isIso (i : ℕ) :
    IsIso (((postnikovStrictZeroBaseLift R f n hn).map (groups R 0)).app i) :=
  groups_map_isIso_of_quasiIsoAt R _ 0 (by
    simpa only [neg_zero] using postnikovStrictZeroBaseLift_quasiIsoAt_zero R f n hn i)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
