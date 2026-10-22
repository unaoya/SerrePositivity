module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovStrictZeroClass

/-!
概要：元の源射の有限切断 class 図式を、底を揃えた有界模型を通して因子分解する。
方針：元の源の持ち上げを非正次数の充満部分圏へ戻し、実 class 関手で合成式を保つ。
規約：源の層射の逆は入力・結論にしない。使われ方：n=1 の実逆 roof の源側比較。
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

def postnikovUpperNonpositiveMap :
    LevelHom (postnikovUpperNonpositiveTower R (B := A) n)
      (postnikovUpperNonpositiveTower R (B := B) n) :=
  TowerDiagram.fullSubcategoryLevelHom (X := A.map (postnikovFunctor R n))
    (Y := B.map (postnikovFunctor R n)) (nonpositiveProperty R)
    (fun i => postnikovComplex_nonpositive R (A.obj i).obj n) (f.map (postnikovFunctor R n))
    (fun i => postnikovComplex_nonpositive R (B.obj i).obj n)

def postnikovStrictZeroBaseNonpositiveLift :
    LevelHom (postnikovUpperNonpositiveTower R (B := A) n)
      (postnikovStrictZeroBaseNonpositiveTower R f n hn) :=
  TowerDiagram.fullSubcategoryLevelHom (X := A.map (postnikovFunctor R n))
    (Y := postnikovStrictZeroBaseTower R f n hn) (nonpositiveProperty R)
    (fun i => postnikovComplex_nonpositive R (A.obj i).obj n)
    (postnikovStrictZeroBaseLift R f n hn) (postnikovStrictZeroBase_nonpositive R f n hn)

lemma postnikovStrictZeroBaseNonpositive_fac :
    (postnikovStrictZeroBaseNonpositiveLift R f n hn).comp
      (postnikovStrictZeroBaseNonpositiveProjection R f n hn) =
        postnikovUpperNonpositiveMap R f n := by
  apply ProSpectrum.levelHom_ext
  intro i
  apply ObjectProperty.hom_ext
  exact congrArg (fun t => t.app i) (postnikovStrictZeroBase_fac R f n hn)

/-- 元の源・標的の有限切断の class 図式の射は、同じ通常模型を通る。 -/
lemma postnikovStrictZeroClass_fac (j : ℤ) (hj : 0 ≤ j) :
    ((postnikovStrictZeroBaseNonpositiveLift R f n hn).map
      (postnikovClassCospanFunctor R j hj)).comp (postnikovStrictZeroClassMap R f n hn j hj) =
        (postnikovUpperNonpositiveMap R f n).map (postnikovClassCospanFunctor R j hj) := by
  change ((postnikovStrictZeroBaseNonpositiveLift R f n hn).map _).comp
    ((postnikovStrictZeroBaseNonpositiveProjection R f n hn).map _) = _
  rw [← TowerDiagram.levelHom_map_comp, postnikovStrictZeroBaseNonpositive_fac]

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
