module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovZeroInverseRoofComparison

/-!
概要：元の roof 細分の零切断は、元の分母・分子・実逆との比較を厳密に保持する。
方針：同じ頂点射を零切断し、元の降下と左 span の式で回収する。
規約：底の逆を選び直さない。使われ方：作用を保つ係数逆を同じ共通底へ移す。
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
  {i m : ℕ} {hi : i ≤ m} (c : NonpositiveInverseRoof R (f.map (postnikovFunctor R 1)) i m hi)
  {k : ℕ} (hm : m ≤ k)

attribute [local instance] oneRoofZero_apex_nonpositive oneRoofZero_targetA_lowerBound
  oneRoofZero_targetB_lowerBound
local instance zeroRefinement_apex_nonpositive :
    (postnikovOneRoofRefine R f c hm).roof.apex.X.IsStrictlyLE 0 :=
  (postnikovOneRoofRefine R f c hm).roof_nonpositive
local instance zeroRefinement_targetB_lowerBound :
    (postnikov R (B.obj k).obj 0).X.IsStrictlyGE 0 := by
  simpa only [neg_zero] using postnikov_lowerBound R (B.obj k).obj 0

def postnikovOneRoofZeroRefineProjection :
    postnikovOneRoofZeroBase R f (postnikovOneRoofRefine R f c hm) ⟶
      postnikovOneRoofZeroBase R f c :=
  postnikovMap R (postnikovOneRoofRefineProjection R f c hm) 0

lemma postnikovOneRoofZeroRefineProjection_numerator :
    postnikovOneRoofZeroRefineProjection R f c hm ≫ postnikovOneRoofZeroNumerator R f c =
      postnikovOneRoofZeroNumerator R f (postnikovOneRoofRefine R f c hm) := by
  have he : postnikovOneRoofRefineProjection R f c hm ≫ (c.roof.numerator ≫
      postnikovTransition R (A.obj i).obj 1 0 (by omega)) =
      (postnikovOneRoofRefine R f c hm).roof.numerator ≫
        postnikovTransition R (A.obj i).obj 1 0 (by omega) :=
    (Category.assoc _ _ _).symm.trans
      (congrArg (fun t => t ≫ postnikovTransition R (A.obj i).obj 1 0 (by omega))
        (postnikovOneRoofRefineProjection_numerator R f c hm))
  exact (postnikovDesc_precompose R 0 (postnikovOneRoofRefineProjection R f c hm) _).trans
    (congrArg (fun t => postnikovDesc R 0 t) he)

lemma postnikovOneRoofZeroRefineProjection_denominator :
    postnikovOneRoofZeroRefineProjection R f c hm ≫ postnikovOneRoofZeroDenominator R f c =
      postnikovOneRoofZeroDenominator R f (postnikovOneRoofRefine R f c hm) ≫
        postnikovMap R (B.transition hm).hom 0 := by
  have he : postnikovOneRoofRefineProjection R f c hm ≫ (c.roof.denominator ≫
      postnikovTransition R (B.obj m).obj 1 0 (by omega)) =
      ((postnikovOneRoofRefine R f c hm).roof.denominator ≫
        postnikovTransition R (B.obj k).obj 1 0 (by omega)) ≫
          postnikovMap R (B.transition hm).hom 0 :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (fun t => t ≫ postnikovTransition R (B.obj m).obj 1 0 (by omega))
        (postnikovOneRoofRefineProjection_denominator R f c hm)).trans
        ((Category.assoc _ _ _).trans
          ((congrArg (fun t => (postnikovOneRoofRefine R f c hm).roof.denominator ≫ t)
            (postnikovTransition_naturality R (B.obj k).obj
              (B.transition hm).hom 1 0 (by omega))).trans (Category.assoc _ _ _).symm)))
  exact (postnikovDesc_precompose R 0 (postnikovOneRoofRefineProjection R f c hm) _).trans
    ((congrArg (fun t => postnikovDesc R 0 t) he).trans
      (postnikovDesc_postcompose R 0 _ (postnikovMap R (B.transition hm).hom 0)).symm)

lemma postnikovOneRoofZeroInverse_refine :
    postnikovOneRoofZeroInverse R f (postnikovOneRoofRefine R f c hm) =
      postnikovMap R (B.transition hm).hom 0 ≫ postnikovOneRoofZeroInverse R f c := by
  have := postnikovOneRoofZeroDenominator_isIso R f c
  have := postnikovOneRoofZeroDenominator_isIso R f (postnikovOneRoofRefine R f c hm)
  have hb : postnikovOneRoofZeroRefineProjection R f c hm ≫
      postnikovOneRoofZeroNumerator R f c =
      postnikovOneRoofZeroDenominator R f (postnikovOneRoofRefine R f c hm) ≫
        postnikovOneRoofZeroInverse R f (postnikovOneRoofRefine R f c hm) :=
    (postnikovOneRoofZeroRefineProjection_numerator R f c hm).trans
      (postnikovOneRoofZeroInverse_denominator R f (postnikovOneRoofRefine R f c hm)).symm
  exact (TowerDiagram.inverse_span_left
    (postnikovOneRoofZeroDenominator R f (postnikovOneRoofRefine R f c hm))
    (postnikovOneRoofZeroRefineProjection R f c hm) (postnikovOneRoofZeroDenominator R f c)
    (postnikovOneRoofZeroNumerator R f c) (postnikovMap R (B.transition hm).hom 0) _
    (postnikovOneRoofZeroRefineProjection_denominator R f c hm) hb).symm

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
