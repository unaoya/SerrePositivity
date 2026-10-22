module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovStrictZeroBase
public import SerrePositivity.KST.LocalizingInvariants.CochainPullbackHomology

/-!
概要：零底を揃えた通常模型の元の右射影は、全ての正の π 次数で各段同型である。
方針：両底の厳密零集中と右脚の次数全射性を、元の kernel 比較へ渡す。
規約：元の π₀ の pro 同型は不要。使われ方：源側の実層射を元の π₁ 射へ同定する。
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

lemma postnikovStrictZeroBaseProjection_quasiIsoAt (j : ℤ) (hj : 0 < j) (i : ℕ) :
    QuasiIsoAt ((postnikovStrictZeroBaseProjection R f n hn).app i).hom (-j) := by
  have hA : (postnikov R (A.obj i).obj 0).X.IsStrictlyGE 0 := by
    change ((postnikovComplex R 0).obj (A.obj i).obj).IsStrictlyGE 0
    simpa only [neg_zero] using postnikovComplex_lowerBound R (A.obj i).obj 0
  have hB : (postnikov R (B.obj i).obj 0).X.IsStrictlyGE 0 := by
    change ((postnikovComplex R 0).obj (B.obj i).obj).IsStrictlyGE 0
    simpa only [neg_zero] using postnikovComplex_lowerBound R (B.obj i).obj 0
  change QuasiIsoAt (pullback.snd (postnikovMap R (f.app i).hom 0).hom
    (postnikovTransition R (B.obj i).obj n 0 hn).hom) (-j)
  exact cochainPullback_snd_quasiIsoAt _ _ (-j)
    ((postnikov R (A.obj i).obj 0).X.isZero_of_isGE 0 (-j) (by omega))
    ((postnikov R (A.obj i).obj 0).X.isZero_of_isGE 0 (-j - 1) (by omega))
    ((postnikov R (B.obj i).obj 0).X.isZero_of_isGE 0 (-j) (by omega))
    ((postnikov R (B.obj i).obj 0).X.isZero_of_isGE 0 (-j - 1) (by omega))

lemma postnikovStrictZeroBaseProjection_groups_isIso (j : ℤ) (hj : 0 < j) (i : ℕ) :
    IsIso (((postnikovStrictZeroBaseProjection R f n hn).map (groups R j)).app i) :=
  groups_map_isIso_of_quasiIsoAt R _ j
    (postnikovStrictZeroBaseProjection_quasiIsoAt R f n hn j hj i)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
