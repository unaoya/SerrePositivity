module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovStrictZeroComparison
public import SerrePositivity.KST.LocalizingInvariants.ProFullSubcategoryLift
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovClassModelMap

/-!
概要：底を揃えた実拡大の pro 逆を、元の Postnikov class の実 cospan 図式へ移す。
方針：元の有界模型を非正次数の充満部分圏へ上げ、元の厳密 class 関手を適用する。
規約：元の源射の層の逆は別工程。使われ方：n=1 の拡大 class と層の比較。
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

def postnikovStrictZeroBaseNonpositiveTower : Tower (NonpositiveAlgebra R) :=
  TowerDiagram.fullSubcategoryTower (nonpositiveProperty R) (postnikovStrictZeroBaseTower R f n hn)
    (postnikovStrictZeroBase_nonpositive R f n hn)

def postnikovUpperNonpositiveTower : Tower (NonpositiveAlgebra R) :=
  TowerDiagram.fullSubcategoryTower (nonpositiveProperty R) (B.map (postnikovFunctor R n))
    (fun i => postnikovComplex_nonpositive R (B.obj i).obj n)

def postnikovStrictZeroBaseNonpositiveProjection :
    LevelHom (postnikovStrictZeroBaseNonpositiveTower R f n hn)
      (postnikovUpperNonpositiveTower R (B := B) n) :=
  TowerDiagram.fullSubcategoryLevelHom (nonpositiveProperty R)
    (postnikovStrictZeroBase_nonpositive R f n hn) (postnikovStrictZeroBaseProjection R f n hn)
    (fun i => postnikovComplex_nonpositive R (B.obj i).obj n)

lemma postnikovStrictZeroBaseNonpositiveProjection_isProIso
    (hf : IsProIso ((f.map (nonpositiveInclusion R)).map (groups R 0))) :
    IsProIso (postnikovStrictZeroBaseNonpositiveProjection R f n hn) :=
  TowerDiagram.fullSubcategoryLevelHom_isProIso (nonpositiveProperty R) _ _ _
    (postnikovStrictZeroBaseProjection_isProIso R f n hn hf)

/-- 元の class・零切断・係数への実三成分を持つ cospan 図式のレベル射。 -/
def postnikovStrictZeroClassMap (j : ℤ) (hj : 0 ≤ j) :=
  (postnikovStrictZeroBaseNonpositiveProjection R f n hn).map
    (postnikovClassCospanFunctor R j hj)

lemma postnikovStrictZeroClassMap_center (j : ℤ) (hj : 0 ≤ j) (i : ℕ) :
    ((postnikovStrictZeroClassMap R f n hn j hj).app i).app .one =
      postnikovDerivationTargetMap R
        ((postnikovStrictZeroBaseNonpositiveProjection R f n hn).app i).hom j hj := rfl

lemma postnikovStrictZeroClassMap_left (j : ℤ) (hj : 0 ≤ j) (i : ℕ) :
    ((postnikovStrictZeroClassMap R f n hn j hj).app i).app .left =
      postnikovPerturbedMap R
        ((postnikovStrictZeroBaseNonpositiveProjection R f n hn).app i).hom j hj := rfl

lemma postnikovStrictZeroClassMap_right (j : ℤ) (hj : 0 ≤ j) (i : ℕ) :
    ((postnikovStrictZeroClassMap R f n hn j hj).app i).app .right =
      postnikovMap R ((postnikovStrictZeroBaseNonpositiveProjection R f n hn).app i).hom j := rfl

lemma postnikovStrictZeroClassMap_isProIso (j : ℤ) (hj : 0 ≤ j)
    (hf : IsProIso ((f.map (nonpositiveInclusion R)).map (groups R 0))) :
    IsProIso (postnikovStrictZeroClassMap R f n hn j hj) :=
  (postnikovStrictZeroBaseNonpositiveProjection_isProIso R f n hn hf).map
    (postnikovClassCospanFunctor R j hj)

/-- 同じ class 図式の元の経路模型の実 pro 逆。 -/
lemma postnikovStrictZeroClassModelMap_isProIso (j : ℤ) (hj : 0 ≤ j)
    (hf : IsProIso ((f.map (nonpositiveInclusion R)).map (groups R 0))) :
    IsProIso ((postnikovStrictZeroBaseNonpositiveProjection R f n hn).map
      (postnikovClassModelFunctor R j hj)) :=
  (postnikovStrictZeroBaseNonpositiveProjection_isProIso R f n hn hf).map
    (postnikovClassModelFunctor R j hj)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
