module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovImageFactorisationNatural
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraProHomology
public import SerrePositivity.KST.LocalizingInvariants.ProLevelwiseInverse

/-!
概要：固定した Postnikov 段の実因子分解を、元の添字・二射・商比較を持つ塔へ送る。
方針：矢印の実塔に、構成済みの実関手と自然変換を適用する。
規約：元の dg 代数射と元の整数群を保持。使われ方：標的側の次数別 π-pro 判定。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovImagePro
open ProExcision
variable (R : Type u) [CommRing R] (X : Tower (Arrow (NonpositiveAlgebra R)))
  (n : ℤ) (hn : 0 ≤ n)

def source : Tower (Mon (Complex R)) := X.map (Arrow.leftFunc ⋙ nonpositiveInclusion R)
def target : Tower (Mon (Complex R)) := X.map (Arrow.rightFunc ⋙ nonpositiveInclusion R)

def original : LevelHom (source R X) (target R X) :=
  TowerDiagram.mapNat X (CategoryTheory.Functor.whiskerRight Arrow.leftToRight
    (nonpositiveInclusion R))

def upperSource : Tower (Mon (Complex R)) := X.map (Arrow.leftFunc ⋙ postnikovFunctor R (n + 1))
def upperTarget : Tower (Mon (Complex R)) := X.map (Arrow.rightFunc ⋙ postnikovFunctor R (n + 1))
def middle : Tower (Mon (Complex R)) := X.map (postnikovImageFactorisationArrowFunctor R n hn)

def left : LevelHom (upperSource R X n) (middle R X n hn) :=
  TowerDiagram.mapNat X (postnikovImageFactorisationArrowSource R n hn)

def right : LevelHom (middle R X n hn) (upperTarget R X n) :=
  TowerDiagram.mapNat X (postnikovImageFactorisationArrowTarget R n hn)

def upperOriginal : LevelHom (upperSource R X n) (upperTarget R X n) :=
  TowerDiagram.mapNat X (CategoryTheory.Functor.whiskerRight Arrow.leftToRight
    (postnikovFunctor R (n + 1)))

def sourceQuotient : LevelHom (source R X) (upperSource R X n) :=
  TowerDiagram.mapNat X (CategoryTheory.Functor.whiskerLeft Arrow.leftFunc
    (postnikovQuotientNatTrans R (n + 1)))

def targetQuotient : LevelHom (target R X) (upperTarget R X n) :=
  TowerDiagram.mapNat X (CategoryTheory.Functor.whiskerLeft Arrow.rightFunc
    (postnikovQuotientNatTrans R (n + 1)))

lemma fac : (left R X n hn).comp (right R X n hn) = upperOriginal R X n := by
  apply ProSpectrum.levelHom_ext
  intro i
  exact postnikovImageFactorisation_fac R (X.obj i).hom.hom n hn

lemma quotient_square : (original R X).comp (targetQuotient R X n) =
    (sourceQuotient R X n).comp (upperOriginal R X n) := by
  apply ProSpectrum.levelHom_ext
  intro i
  exact (postnikovQuotient_naturality R (X.obj i).hom.hom (n + 1)).symm

lemma sourceQuotient_groups_isIso (j : ℤ) (hj : j ≤ n + 1) (i : ℕ) :
    IsIso (((sourceQuotient R X n).map (groups R j)).app i) :=
  postnikovQuotient_groups_isIso R (X.obj i).left.obj (n + 1) j hj

lemma targetQuotient_groups_isIso (j : ℤ) (hj : j ≤ n + 1) (i : ℕ) :
    IsIso (((targetQuotient R X n).map (groups R j)).app i) :=
  postnikovQuotient_groups_isIso R (X.obj i).right.obj (n + 1) j hj

lemma left_groups_isIso (j : ℤ) (hj : j ≤ n) (i : ℕ) :
    IsIso (((left R X n hn).map (groups R j)).app i) :=
  groups_map_isIso_of_quasiIsoAt R _ j
    (postnikovImageFactorisationSource_quasiIsoAt R (X.obj i).hom.hom n hn (-j) (by omega))

lemma left_groups_surjective (j : ℤ) (hj : j ≤ n + 1) (i : ℕ) :
    Function.Surjective (((left R X n hn).map (groups R j)).app i).hom :=
  (postnikovImageFactorisationArrowSource_connected R n hn (X.obj i)).2 j hj

lemma right_groups_injective_succ (i : ℕ) :
    Function.Injective (((right R X n hn).map (groups R (n + 1))).app i).hom :=
  postnikovImageFactorisationTarget_groups_injective_succ R (X.obj i).hom.hom n hn

lemma middle_groups_subsingleton (j : ℤ) (hj : n + 1 < j) (i : ℕ) :
    Subsingleton (((middle R X n hn).map (groups R j)).obj i) := by
  apply groups_subsingleton_of_homology_zero R _ j
  exact postnikovImageFactorisationObject_homology_zero R (X.obj i).hom.hom n hn (-j) (by omega)

lemma upperTarget_groups_subsingleton (j : ℤ) (hj : n + 1 < j) (i : ℕ) :
    Subsingleton (((upperTarget R X n).map (groups R j)).obj i) :=
  postnikov_groups_subsingleton R (X.obj i).right.obj (n + 1) j hj

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovImagePro
