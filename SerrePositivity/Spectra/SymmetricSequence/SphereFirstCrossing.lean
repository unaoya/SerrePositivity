module

public import SerrePositivity.CategoryTheory.Monoidal.TensorPowerFirstCrossingAction
public import SerrePositivity.Spectra.SymmetricSequence.SpherePermutationAction

/-! # 円の先頭因子を末尾へ移す巡回置換

隣接交換で構成した移動を、既存の球面の対称群作用とbraidingへ接続する。
一般の二つの正次数のブロック全体の交換はまだ含まない。
-/

@[expose] public section

universe u

noncomputable section

namespace SerrePositivity.PointedSimplicialSet

open CategoryTheory CategoryTheory.MonoidalCategory

/-- 円の反復smashの先頭因子を末尾へ移す同型。 -/
def sphereFirstCrossingIso (n : ℕ) : spherePower.{u} (n + 1) ≅ spherePower.{u} (n + 1) :=
  TensorPowers.moveFirstIso (circle : PointedSimplicialSet.{u}) n

/-- 隣接交換の列は、円と尾のbraidingと連結の合成に一致する。 -/
lemma sphereFirstCrossingIso_braiding (n : ℕ) :
    (sphereFirstCrossingIso.{u} n).hom =
      (β_ (circle : PointedSimplicialSet.{u}) (spherePower.{u} n)).hom ≫
        (spherePower.{u} n ◁ (ρ_ (circle : PointedSimplicialSet.{u})).inv) ≫
        (spherePowerAppendIso.{u} n 1).hom :=
  TensorPowers.moveFirstIso_braiding (circle : PointedSimplicialSet.{u}) n

/-- 先頭を末尾へ送る有限置換の作用は、円の隣接交換による移動。 -/
lemma spherePermutationAction_firstToLast (n : ℕ) :
    (spherePermutationAction.{u} (n + 1) (Coxeter.firstToLastPerm n)).asIso.hom =
      (sphereFirstCrossingIso.{u} n).hom :=
  TensorPowers.permutationAction_firstToLast (circle : PointedSimplicialSet.{u}) n

/-- 逆向きの巡回置換の球面への作用と、braidingによる移動の比較。 -/
lemma spherePermutationAction_rotate_symm (n : ℕ) :
    (spherePermutationAction.{u} (n + 1) (finRotate (n + 1)).symm).asIso.hom =
      (β_ (circle : PointedSimplicialSet.{u}) (spherePower.{u} n)).hom ≫
        (spherePower.{u} n ◁ (ρ_ (circle : PointedSimplicialSet.{u})).inv) ≫
        (spherePowerAppendIso.{u} n 1).hom :=
  TensorPowers.permutationAction_rotate_symm (circle : PointedSimplicialSet.{u}) n

end SerrePositivity.PointedSimplicialSet
