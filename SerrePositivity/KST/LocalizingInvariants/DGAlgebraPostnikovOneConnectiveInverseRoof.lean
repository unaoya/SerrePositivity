module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraNormalizedClassInverseRoof
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovConnectiveRoofReflection
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraConnectiveProRoofComposition

/-!
概要：元の一切断射の実 roof 逆を、connective 準同型反転だけで提供する。
方針：元の class 比較・有界商射の実 roof と、元の右射影の逆を合成する。
規約：実 span を評価より先に選ぶ。使われ方：元の IsKConnective 不変量値の逆。
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

lemma postnikovNormalizedSource_hasConnectiveRoofProInverse
    (hf : IsProIso ((f.map (nonpositiveInclusion R)).map (groups R 1))) :
    HasConnectiveRoofProInverse R (D := D)
      (postnikovStrictZeroBaseLift R f 1 (by omega))
      (fun i => nonpositive_isConnective R
        ((postnikovStrictZeroBaseNonpositiveTower R f 1 (by omega)).obj i).obj) := by
  let a := postnikovStrictZeroBaseNonpositiveLift R f 1 (by omega)
  have hc := postnikovClassModelMap_reflects_connectiveRoofProInverse R a 0 (by omega)
    (postnikovNormalizedClass_hasConnectiveRoofProInverse R f (D := D) hf)
  apply postnikovMap_reflects_connectiveRoofProInverse_of_bounded R a 1 ?_ ?_ hc
  · intro i
    change (postnikov R (A.obj i).obj 1).X.IsGE (-1)
    have : (postnikov R (A.obj i).obj 1).X.IsStrictlyGE (-1) :=
      postnikovComplex_lowerBound R (A.obj i).obj 1
    infer_instance
  · intro i
    change ((postnikovStrictZeroBaseTower R f 1 (by omega)).obj i).X.IsGE (-1)
    have := postnikovStrictZeroBase_lowerBound R f 1 (by omega) i
    infer_instance

lemma postnikovOneMap_hasConnectiveRoofProInverse
    (h₀ : IsProIso ((f.map (nonpositiveInclusion R)).map (groups R 0)))
    (h₁ : IsProIso ((f.map (nonpositiveInclusion R)).map (groups R 1))) :
    HasConnectiveRoofProInverse R (D := D) (f.map (postnikovFunctor R 1))
      (fun i => postnikov_isConnective R (B.obj i).obj 1) := by
  have ha := postnikovNormalizedSource_hasConnectiveRoofProInverse R f (D := D) h₁
  have hb := hasConnectiveRoofProInverse_of_proIso R (D := D)
    (fun i => postnikov_isConnective R (B.obj i).obj 1)
    (postnikovStrictZeroBaseProjection_isProIso R f 1 (by omega) h₀)
  have hc := ha.comp R hb
  rw [postnikovStrictZeroBase_fac] at hc
  exact hc

lemma nonpositiveMap_hasConnectiveRoofProInverse_of_oneBounded
    (hA : ∀ i, (A.obj i).obj.X.IsGE (-1)) (hB : ∀ i, (B.obj i).obj.X.IsGE (-1))
    (h₀ : IsProIso ((f.map (nonpositiveInclusion R)).map (groups R 0)))
    (h₁ : IsProIso ((f.map (nonpositiveInclusion R)).map (groups R 1))) :
    HasConnectiveRoofProInverse R (D := D) (f.map (nonpositiveInclusion R))
      (fun i => nonpositive_isConnective R (B.obj i).obj) :=
  postnikovMap_reflects_connectiveRoofProInverse_of_bounded R f 1 hA hB
    (postnikovOneMap_hasConnectiveRoofProInverse R f (D := D) h₀ h₁)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
