module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraNormalizedClassInverseRoof
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCellNativeRoofReflection
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraCellNativeRoofPostcompose

/-!
概要：元の π₀・π₁ の pro 同型から、元の一切断射の実三角形付き roof 逆を構成する。
方針：正規化した class の逆を二つの準同型比較で反映し、元の右射影の逆と合成。
規約：左の cell 持ち上げと右の乗法的経路を保持。使われ方：高次有限段の底変更。
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

lemma postnikovNormalizedSource_hasCellNativeRoofProInverse
    (hf : IsProIso ((f.map (nonpositiveInclusion R)).map (groups R 1))) :
    HasCellNativeRoofProInverse R
      (postnikovStrictZeroBaseLift R f 1 (by omega)) := by
  let a := postnikovStrictZeroBaseNonpositiveLift R f 1 (by omega)
  have hc := postnikovClassModelMap_reflects_cellNativeRoofProInverse R a 0 (by omega)
    ((postnikovNormalizedClass_hasNativeRoofProInverse R f hf).cellNative R)
  apply postnikovMap_reflects_cellNativeRoofProInverse_of_bounded R a 1 ?_ ?_ hc
  · intro i
    change (postnikov R (A.obj i).obj 1).X.IsGE (-1)
    have : (postnikov R (A.obj i).obj 1).X.IsStrictlyGE (-1) :=
      postnikovComplex_lowerBound R (A.obj i).obj 1
    infer_instance
  · intro i
    change ((postnikovStrictZeroBaseTower R f 1 (by omega)).obj i).X.IsGE (-1)
    have := postnikovStrictZeroBase_lowerBound R f 1 (by omega) i
    infer_instance

lemma postnikovOneMap_hasCellNativeRoofProInverse
    (h₀ : IsProIso ((f.map (nonpositiveInclusion R)).map (groups R 0)))
    (h₁ : IsProIso ((f.map (nonpositiveInclusion R)).map (groups R 1))) :
    HasCellNativeRoofProInverse R (f.map (postnikovFunctor R 1)) := by
  have ha := postnikovNormalizedSource_hasCellNativeRoofProInverse R f h₁
  have hc := ha.postcompose R _ _
    (postnikovStrictZeroBaseProjection_isProIso R f 1 (by omega) h₀)
  rw [postnikovStrictZeroBase_fac] at hc
  exact hc

lemma nonpositiveMap_hasCellNativeRoofProInverse_of_oneBounded
    (hA : ∀ i, (A.obj i).obj.X.IsGE (-1)) (hB : ∀ i, (B.obj i).obj.X.IsGE (-1))
    (h₀ : IsProIso ((f.map (nonpositiveInclusion R)).map (groups R 0)))
    (h₁ : IsProIso ((f.map (nonpositiveInclusion R)).map (groups R 1))) :
    HasCellNativeRoofProInverse R (f.map (nonpositiveInclusion R)) :=
  postnikovMap_reflects_cellNativeRoofProInverse_of_bounded R f 1 hA hB
    (postnikovOneMap_hasCellNativeRoofProInverse R f h₀ h₁)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
