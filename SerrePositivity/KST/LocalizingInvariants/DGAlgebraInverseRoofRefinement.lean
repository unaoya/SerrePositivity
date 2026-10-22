module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraInverseRoofRefinementLift

/-!
概要：元の非正次数逆 roof の全データを、任意の後続段へ細分する。
方針：実 pullback の左持ち上げと、元の指定右経路の前合成を組み合わせる。
規約：元の経路射そのものを保持。使われ方：係数逆の段に合わせた共通作用底。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory HomologicalComplex
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.NonpositiveInverseRoof
open ProExcision
variable (R : Type u) [CommRing R] {X Y : Tower (Mon (Complex R))} {f : LevelHom X Y}
  {i m : ℕ} {hi : i ≤ m} (c : NonpositiveInverseRoof R f i m hi)
  {k : ℕ} (hm : m ≤ k)

def refinementRightPath : Path.Witness R
    ((refinementRoof R c hm).numerator ≫ f.app i)
    ((refinementRoof R c hm).denominator ≫ Y.transition (hi.trans hm)) where
  hom := refinementProjection R c hm ≫ c.rightPath.hom
  source_eq := by
    have hs := (c.rightPath.precomp (refinementProjection R c hm)).source_eq
    exact hs.trans (Category.assoc _ _ _).symm
  target_eq := by
    have ht := (c.rightPath.precomp (refinementProjection R c hm)).target_eq
    exact ht.trans ((Category.assoc _ _ _).symm.trans
      ((congrArg (fun t => t ≫ Y.transition hi)
        (refinementProjection_denominator R c hm)).trans
        ((Category.assoc _ _ _).trans
          (congrArg (fun t => (refinementRoof R c hm).denominator ≫ t)
            (Y.transition_comp hm hi)))))

lemma refinementRightPath_hom : (refinementRightPath R c hm).hom =
    refinementProjection R c hm ≫ c.rightPath.hom := rfl

variable [(X.obj k).X.IsStrictlyLE 0] [(Y.obj k).X.IsStrictlyLE 0]

def refine : NonpositiveInverseRoof R f i k (hi.trans hm) where
  roof := refinementRoof R c hm
  roof_nonpositive := refinementRoof_nonpositive R c hm
  source := refinementSource R c hm
  source_nonpositive := refinementSource_nonpositive R c hm
  sourceProjection := refinementSourceProjection R c hm
  sourceProjection_epi := refinementSourceProjection_epi R c hm
  sourceProjection_quasiIso := refinementSourceProjection_quasiIso R c hm
  sourceLift := refinementLift R c hm
  source_denominator := refinementLift_denominator R c hm
  source_numerator := refinementLift_numerator R c hm
  rightPath := refinementRightPath R c hm

lemma refine_roof : (refine R c hm).roof = refinementRoof R c hm := rfl

lemma refine_source : (refine R c hm).source = refinementSource R c hm := rfl

lemma refine_rightPath_hom : (refine R c hm).rightPath.hom =
    refinementProjection R c hm ≫ c.rightPath.hom := rfl

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.NonpositiveInverseRoof
