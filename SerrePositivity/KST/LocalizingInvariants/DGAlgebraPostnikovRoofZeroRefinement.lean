module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovRoofZeroSpan
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraInverseRoofRefinement

/-!
概要：任意の有限段の実 roof 細分を、元の二脚を保つ零底の可換正方形へ送る。
方針：元の細分射影の両厳密式を一般の零脚自然性へ渡す。
規約：同じ細分と元の遷移を保持。使われ方：高次係数逆との共通零底。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovRoofZeroSpan
open ProExcision
variable (R : Type u) [CommRing R] (n : ℤ) (hn : 0 ≤ n)
  {A B : Tower (NonpositiveAlgebra R)} (f : LevelHom A B)
  {i m : ℕ} {hi : i ≤ m} (c : NonpositiveInverseRoof R (f.map (postnikovFunctor R n)) i m hi)
  {k : ℕ} (hm : m ≤ k)

local instance original_apex_nonpositive : c.roof.apex.X.IsStrictlyLE 0 := c.roof_nonpositive
local instance refined_sourceLevel_nonpositive : ((A.map (postnikovFunctor R n)).obj k).X.IsStrictlyLE 0 :=
  postnikov_nonpositive R (A.obj k).obj n
local instance refined_targetLevel_nonpositive : ((B.map (postnikovFunctor R n)).obj k).X.IsStrictlyLE 0 :=
  postnikov_nonpositive R (B.obj k).obj n
local instance refined_apex_nonpositive : (c.refinementRoof R hm).apex.X.IsStrictlyLE 0 :=
  c.refinementRoof_nonpositive R hm

lemma refinement_denominator_square :
    postnikovMap R (c.refinementProjection R hm) 0 ≫ denominator R n hn f c =
      denominator R n hn f (c.refine R hm) ≫ postnikovMap R (B.transition hm).hom 0 :=
  postnikovZeroLeg_square R n hn (B.obj m) (B.obj k) c.roof.denominator
    (c.refinementProjection R hm) (c.refine R hm).roof.denominator
    (B.transition hm) (c.refinementProjection_denominator R hm)

lemma refinement_numerator_square :
    postnikovMap R (c.refinementProjection R hm) 0 ≫ numerator R n hn f c =
      numerator R n hn f (c.refine R hm) := by
  have h : c.refinementProjection R hm ≫
      (c.roof.numerator ≫ postnikovTransition R (A.obj i).obj n 0 hn) =
      (c.refine R hm).roof.numerator ≫ postnikovTransition R (A.obj i).obj n 0 hn :=
    (Category.assoc _ _ _).symm.trans
      (congrArg (fun t => t ≫ postnikovTransition R (A.obj i).obj n 0 hn)
        (c.refinementProjection_numerator R hm))
  exact (postnikovDesc_precompose R 0 (c.refinementProjection R hm) _).trans
    (congrArg (fun t => postnikovDesc R 0 t) h)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovRoofZeroSpan
