module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraInverseRoofRefinement
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovTwoRoofDenominator

/-!
概要：元の一切断逆の全データを、指定した後続段へ非正次数のまま細分する。
方針：元の Postnikov 塔の遷移を一般の実 roof 細分へ渡す。
規約：元の右経路射と左持ち上げを保持。使われ方：π₂ 係数の実共通作用底。
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

local instance refinementSourceLevel_nonpositive :
    ((A.map (postnikovFunctor R 1)).obj k).X.IsStrictlyLE 0 :=
  postnikovComplex_nonpositive R (A.obj k).obj 1

local instance refinementTargetLevel_nonpositive :
    ((B.map (postnikovFunctor R 1)).obj k).X.IsStrictlyLE 0 :=
  postnikovComplex_nonpositive R (B.obj k).obj 1

def postnikovOneRoofRefine :
    NonpositiveInverseRoof R (f.map (postnikovFunctor R 1)) i k (hi.trans hm) :=
  c.refine R hm

def postnikovOneRoofRefineProjection : (postnikovOneRoofRefine R f c hm).roof.apex ⟶
    c.roof.apex := c.refinementProjection R hm

lemma postnikovOneRoofRefineProjection_denominator :
    postnikovOneRoofRefineProjection R f c hm ≫ c.roof.denominator =
      (postnikovOneRoofRefine R f c hm).roof.denominator ≫
        postnikovMap R (B.transition hm).hom 1 := c.refinementProjection_denominator R hm

lemma postnikovOneRoofRefineProjection_numerator :
    postnikovOneRoofRefineProjection R f c hm ≫ c.roof.numerator =
      (postnikovOneRoofRefine R f c hm).roof.numerator := rfl

lemma postnikovOneRoofRefine_rightPath : (postnikovOneRoofRefine R f c hm).rightPath.hom =
    postnikovOneRoofRefineProjection R f c hm ≫ c.rightPath.hom := rfl

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
