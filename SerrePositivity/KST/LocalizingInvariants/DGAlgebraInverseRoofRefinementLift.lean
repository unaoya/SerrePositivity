module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraInverseRoofRefinementObjects

/-!
概要：元の逆 roof の左持ち上げを、後続段の二つの実 pullback の間へ移す。
方針：元の左三角形と元の塔の自然性から、実代数 pullback の持ち上げを構成する。
規約：元の sourceProjection と両三角形を保持。使われ方：係数逆の段への roof 細分。
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

lemma refinementLift_condition :
    (refinementSourceProjection R c hm ≫ f.app k) ≫ Y.transition hm =
      (refinementSourceUpper R c hm ≫ c.sourceLift) ≫ c.roof.denominator := by
  calc
    _ = refinementSourceProjection R c hm ≫ (X.transition hm ≫ f.app m) :=
      (Category.assoc _ _ _).trans
        (congrArg (fun t => refinementSourceProjection R c hm ≫ t) (f.naturality hm).symm)
    _ = (refinementSourceUpper R c hm ≫ c.sourceProjection) ≫ f.app m :=
      (Category.assoc _ _ _).symm.trans
        (congrArg (fun t => t ≫ f.app m) (refinementSource_condition R c hm))
    _ = _ := (Category.assoc _ _ _).trans
      ((congrArg (fun t => refinementSourceUpper R c hm ≫ t) c.source_denominator.symm).trans
        (Category.assoc _ _ _).symm)

def refinementLift : refinementSource R c hm ⟶ (refinementRoof R c hm).apex :=
  MonoidPullback.lift (Y.transition hm) c.roof.denominator
    (refinementSourceProjection R c hm ≫ f.app k)
    (refinementSourceUpper R c hm ≫ c.sourceLift) (refinementLift_condition R c hm)

lemma refinementLift_projection : refinementLift R c hm ≫ refinementProjection R c hm =
    refinementSourceUpper R c hm ≫ c.sourceLift := MonoidPullback.lift_snd _ _ _ _ _

lemma refinementLift_denominator : refinementLift R c hm ≫
    (refinementRoof R c hm).denominator = refinementSourceProjection R c hm ≫ f.app k := by
  rw [refinementRoof_denominator]
  exact MonoidPullback.lift_fst _ _ _ _ _

lemma refinementLift_numerator : refinementLift R c hm ≫ (refinementRoof R c hm).numerator =
    refinementSourceProjection R c hm ≫ X.transition (hi.trans hm) := by
  calc
    _ = (refinementLift R c hm ≫ refinementProjection R c hm) ≫ c.roof.numerator :=
      (Category.assoc _ _ _).symm
    _ = (refinementSourceUpper R c hm ≫ c.sourceLift) ≫ c.roof.numerator :=
      congrArg (fun t => t ≫ c.roof.numerator) (refinementLift_projection R c hm)
    _ = refinementSourceUpper R c hm ≫ (c.sourceProjection ≫ X.transition hi) :=
      (Category.assoc _ _ _).trans
        (congrArg (fun t => refinementSourceUpper R c hm ≫ t) c.source_numerator)
    _ = (refinementSourceProjection R c hm ≫ X.transition hm) ≫ X.transition hi :=
      (Category.assoc _ _ _).symm.trans
        (congrArg (fun t => t ≫ X.transition hi) (refinementSource_condition R c hm).symm)
    _ = _ := (Category.assoc _ _ _).trans
      (congrArg (fun t => refinementSourceProjection R c hm ≫ t) (X.transition_comp hm hi))

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.NonpositiveInverseRoof
