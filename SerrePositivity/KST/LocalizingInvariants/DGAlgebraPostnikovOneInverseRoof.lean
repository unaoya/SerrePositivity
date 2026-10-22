module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraNormalizedClassInverseRoof
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovRoofReflection
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraProRoofComposition

/-!
概要：元の π₀・π₁ の pro 同型から、元の一切断射の逆を実 dg roof として構成する。
方針：正規化した class の逆を二つの準同型比較で反映し、元の右射影の逆と合成。
規約：同じ span を全ての反転関手で評価する。使われ方：高次有限段の底変更。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
open ProExcision
variable (R : Type u) [CommRing R] {A B : Tower (NonpositiveAlgebra R)} (f : LevelHom A B)
  {D : Type v} [Category.{w} D]

lemma postnikovNormalizedSource_hasRoofProInverse
    (hf : IsProIso ((f.map (nonpositiveInclusion R)).map (groups R 1))) :
    HasSurjectiveRoofProInverse R (D := D)
      (postnikovStrictZeroBaseLift R f 1 (by omega)) := by
  let a := postnikovStrictZeroBaseNonpositiveLift R f 1 (by omega)
  have hc := postnikovClassModelMap_reflects_roofProInverse R a 0 (by omega)
    (postnikovNormalizedClass_hasRoofProInverse R f (D := D) hf)
  apply postnikovMap_reflects_roofProInverse_of_bounded R a 1 ?_ ?_ hc
  · intro i
    change (postnikov R (A.obj i).obj 1).X.IsGE (-1)
    have : (postnikov R (A.obj i).obj 1).X.IsStrictlyGE (-1) :=
      postnikovComplex_lowerBound R (A.obj i).obj 1
    infer_instance
  · intro i
    change ((postnikovStrictZeroBaseTower R f 1 (by omega)).obj i).X.IsGE (-1)
    have := postnikovStrictZeroBase_lowerBound R f 1 (by omega) i
    infer_instance

lemma postnikovOneMap_hasRoofProInverse
    (h₀ : IsProIso ((f.map (nonpositiveInclusion R)).map (groups R 0)))
    (h₁ : IsProIso ((f.map (nonpositiveInclusion R)).map (groups R 1))) :
    HasSurjectiveRoofProInverse R (D := D) (f.map (postnikovFunctor R 1)) := by
  have ha := postnikovNormalizedSource_hasRoofProInverse R f (D := D) h₁
  have hb := hasRoofProInverse_of_proIso R (D := D)
    (postnikovStrictZeroBaseProjection_isProIso R f 1 (by omega) h₀)
  have hc := ha.comp R hb
  rw [postnikovStrictZeroBase_fac] at hc
  exact hc

lemma nonpositiveMap_hasRoofProInverse_of_oneBounded
    (hA : ∀ i, (A.obj i).obj.X.IsGE (-1)) (hB : ∀ i, (B.obj i).obj.X.IsGE (-1))
    (h₀ : IsProIso ((f.map (nonpositiveInclusion R)).map (groups R 0)))
    (h₁ : IsProIso ((f.map (nonpositiveInclusion R)).map (groups R 1))) :
    HasSurjectiveRoofProInverse R (D := D) (f.map (nonpositiveInclusion R)) :=
  postnikovMap_reflects_roofProInverse_of_bounded R f 1 hA hB
    (postnikovOneMap_hasRoofProInverse R f (D := D) h₀ h₁)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
