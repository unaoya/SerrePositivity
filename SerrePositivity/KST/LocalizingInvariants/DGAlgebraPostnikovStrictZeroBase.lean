module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovZeroBaseFactor
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPullbackTowerComparison
public import SerrePositivity.KST.LocalizingInvariants.CochainPullbackBounds

/-!
概要：元の零切断を底に持つ通常模型と、元の有限切断射の実因子分解を構成する。
方針：元の cospan の通常 pullback を使い、右射影の実代数 pro 逆を構成する。
規約：値への移送に IsKConnective は不要。使われ方：有限層の class 比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
open ProExcision
variable (R : Type u) [CommRing R] {A B : Tower (NonpositiveAlgebra R)}
  (f : LevelHom A B) (n : ℤ) (hn : 0 ≤ n)

def postnikovStrictZeroBaseTower : Tower (Mon (Complex R)) :=
  MonoidPullback.pullbackTower (f.map (postnikovFunctor R 0))
    (postnikovTransitionLevelHom R B n 0 hn)

def postnikovStrictZeroBaseProjection :
    LevelHom (postnikovStrictZeroBaseTower R f n hn) (B.map (postnikovFunctor R n)) :=
  MonoidPullback.rightProjection _ _

def postnikovStrictZeroBaseLift :
    LevelHom (A.map (postnikovFunctor R n)) (postnikovStrictZeroBaseTower R f n hn) :=
  MonoidPullback.squareLift _ _ (postnikovTransitionLevelHom R A n 0 hn)
    (f.map (postnikovFunctor R n)) (postnikovZeroBase_square R f n hn)

lemma postnikovStrictZeroBase_fac :
    (postnikovStrictZeroBaseLift R f n hn).comp (postnikovStrictZeroBaseProjection R f n hn) =
      f.map (postnikovFunctor R n) := MonoidPullback.squareLift_comp_right _ _ _ _ _

lemma postnikovStrictZeroBaseProjection_isProIso
    (hf : IsProIso ((f.map (nonpositiveInclusion R)).map (groups R 0))) :
    IsProIso (postnikovStrictZeroBaseProjection R f n hn) :=
  MonoidPullback.rightProjection_isProIso _ _ (postnikovZeroMap_isProIso R f hf)

lemma postnikovStrictZeroBase_nonpositive (i : ℕ) :
    ((postnikovStrictZeroBaseTower R f n hn).obj i).X.IsStrictlyLE 0 := by
  have hA : (postnikov R (A.obj i).obj 0).X.IsStrictlyLE 0 := by
    change ((postnikovComplex R 0).obj (A.obj i).obj).IsStrictlyLE 0
    exact postnikovComplex_nonpositive R (A.obj i).obj 0
  have hB : (postnikov R (B.obj i).obj n).X.IsStrictlyLE 0 := by
    change ((postnikovComplex R n).obj (B.obj i).obj).IsStrictlyLE 0
    exact postnikovComplex_nonpositive R (B.obj i).obj n
  exact @CochainPullback.isStrictlyLE R _ _ _ _ _ _ 0 hA hB

lemma postnikovStrictZeroBase_lowerBound (i : ℕ) :
    ((postnikovStrictZeroBaseTower R f n hn).obj i).X.IsStrictlyGE (-n) := by
  have hA : (postnikov R (A.obj i).obj 0).X.IsStrictlyGE 0 := by
    change ((postnikovComplex R 0).obj (A.obj i).obj).IsStrictlyGE 0
    simpa only [neg_zero] using postnikovComplex_lowerBound R (A.obj i).obj 0
  have hA' := CochainComplex.isStrictlyGE_of_ge
    (postnikov R (A.obj i).obj 0).X (-n) 0 (by omega)
  have hB : (postnikov R (B.obj i).obj n).X.IsStrictlyGE (-n) := by
    change ((postnikovComplex R n).obj (B.obj i).obj).IsStrictlyGE (-n)
    exact postnikovComplex_lowerBound R (B.obj i).obj n
  exact @CochainPullback.isStrictlyGE R _ _ _ _ _ _ (-n) hA' hB

variable (Φ : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u + 1} ⟶ Sp.{u + 1})

lemma postnikovStrictZeroBaseProjection_value_isProIso
    (hf : IsProIso ((f.map (nonpositiveInclusion R)).map (groups R 0))) :
    IsProIso ((postnikovStrictZeroBaseProjection R f n hn).map (invariantFunctor R Φ)) :=
  (postnikovStrictZeroBaseProjection_isProIso R f n hn hf).map (invariantFunctor R Φ)

lemma postnikovStrictZeroBaseProjection_value_piProEquivalence
    (hf : IsProIso ((f.map (nonpositiveInclusion R)).map (groups R 0))) :
    ProSpectrum.IsPiProEquivalence
      ((postnikovStrictZeroBaseProjection R f n hn).map (invariantFunctor R Φ)) :=
  ProSpectrum.piProEquivalence_of_proIso
    (postnikovStrictZeroBaseProjection_value_isProIso R f n hn Φ hf)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
