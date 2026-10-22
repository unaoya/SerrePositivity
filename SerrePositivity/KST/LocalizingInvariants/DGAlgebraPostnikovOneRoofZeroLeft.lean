module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovOneRoofZeroBase
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovDescComposition
public import SerrePositivity.KST.LocalizingInvariants.ProInverseEventualUniqueness

/-!
概要：元の一切断 roof の零切断の逆は、元の零切断射の左逆三角形を保持する。
方針：元の左細分も零切断へ降ろし、同じ実持ち上げの二つの厳密な式を使う。
規約：元の sourceProjection と左持ち上げを保持。使われ方：他の底逆との eventual 一致。
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

attribute [local instance] oneRoofZero_apex_nonpositive oneRoofZero_targetA_lowerBound
  oneRoofZero_targetB_lowerBound

local instance oneRoofZero_source_nonpositive : c.source.X.IsStrictlyLE 0 := c.source_nonpositive
local instance oneRoofZero_targetAm_lowerBound :
    (postnikov R (A.obj m).obj 0).X.IsStrictlyGE 0 := by
  simpa only [neg_zero] using postnikov_lowerBound R (A.obj m).obj 0
local instance oneRoofZero_targetAm_nonpositive : (postnikov R (A.obj m).obj 0).X.IsStrictlyLE 0 :=
  postnikovComplex_nonpositive R (A.obj m).obj 0

def postnikovOneRoofZeroSourceProjection : postnikov R c.source 0 ⟶
    postnikov R (A.obj m).obj 0 :=
  postnikovDesc R 0 (c.sourceProjection ≫ postnikovTransition R (A.obj m).obj 1 0 (by omega))

def postnikovOneRoofZeroSourceLift : postnikov R c.source 0 ⟶ postnikovOneRoofZeroBase R f c :=
  postnikovMap R c.sourceLift 0

lemma postnikovOneRoofZeroSourceProjection_isIso :
    IsIso (postnikovOneRoofZeroSourceProjection R f c) := by
  have hp := groups_map_isIso_of_quasiIso R c.sourceProjection c.sourceProjection_quasiIso 0
  have ht := groups_map_isIso_of_quasiIsoAt R
    (postnikovTransition R (A.obj m).obj 1 0 (by omega)) 0
    (postnikovTransition_quasiIsoAt R (A.obj m).obj 1 0 (by omega) 0 (by omega))
  apply postnikovDesc_zero_isIso_of_groups R
  rw [Functor.map_comp]
  infer_instance

lemma postnikovOneRoofZeroSourceLift_denominator : postnikovOneRoofZeroSourceLift R f c ≫
    postnikovOneRoofZeroDenominator R f c =
      postnikovOneRoofZeroSourceProjection R f c ≫ postnikovMap R (f.app m).hom 0 := by
  have he : c.sourceLift ≫ (c.roof.denominator ≫
      postnikovTransition R (B.obj m).obj 1 0 (by omega)) =
      (c.sourceProjection ≫ postnikovTransition R (A.obj m).obj 1 0 (by omega)) ≫
        postnikovMap R (f.app m).hom 0 := by
    have hd : c.sourceLift ≫ c.roof.denominator =
        c.sourceProjection ≫ postnikovMap R (f.app m).hom 1 := c.source_denominator
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun t => t ≫ postnikovTransition R (B.obj m).obj 1 0 (by omega)) hd).trans
        ((Category.assoc _ _ _).trans
          ((congrArg (fun t => c.sourceProjection ≫ t)
            (postnikovTransition_naturality R (A.obj m).obj (f.app m).hom 1 0 (by omega))).trans
              (Category.assoc _ _ _).symm)))
  exact (postnikovDesc_precompose R 0 c.sourceLift _).trans
    ((congrArg (fun t => postnikovDesc R 0 t) he).trans
      (postnikovDesc_postcompose R 0 _ (postnikovMap R (f.app m).hom 0)).symm)

lemma postnikovOneRoofZeroSourceLift_numerator : postnikovOneRoofZeroSourceLift R f c ≫
    postnikovOneRoofZeroNumerator R f c = postnikovOneRoofZeroSourceProjection R f c ≫
      postnikovMap R (A.transition hi).hom 0 := by
  have he : c.sourceLift ≫ (c.roof.numerator ≫
      postnikovTransition R (A.obj i).obj 1 0 (by omega)) =
      (c.sourceProjection ≫ postnikovTransition R (A.obj m).obj 1 0 (by omega)) ≫
        postnikovMap R (A.transition hi).hom 0 := by
    have hn : c.sourceLift ≫ c.roof.numerator =
        c.sourceProjection ≫ postnikovMap R (A.transition hi).hom 1 := c.source_numerator
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun t => t ≫ postnikovTransition R (A.obj i).obj 1 0 (by omega)) hn).trans
        ((Category.assoc _ _ _).trans
          ((congrArg (fun t => c.sourceProjection ≫ t)
            (postnikovTransition_naturality R (A.obj m).obj
              (A.transition hi).hom 1 0 (by omega))).trans (Category.assoc _ _ _).symm)))
  exact (postnikovDesc_precompose R 0 c.sourceLift _).trans
    ((congrArg (fun t => postnikovDesc R 0 t) he).trans
      (postnikovDesc_postcompose R 0 _ (postnikovMap R (A.transition hi).hom 0)).symm)

lemma postnikovOneRoofZeroInverse_left : postnikovMap R (f.app m).hom 0 ≫
    postnikovOneRoofZeroInverse R f c = postnikovMap R (A.transition hi).hom 0 := by
  have := postnikovOneRoofZeroSourceProjection_isIso R f c
  have := postnikovOneRoofZeroDenominator_isIso R f c
  exact TowerDiagram.inverse_span_left (postnikovOneRoofZeroSourceProjection R f c)
    (postnikovOneRoofZeroSourceLift R f c) (postnikovOneRoofZeroDenominator R f c)
    (postnikovOneRoofZeroNumerator R f c) _ _
    (postnikovOneRoofZeroSourceLift_denominator R f c)
    (postnikovOneRoofZeroSourceLift_numerator R f c)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
