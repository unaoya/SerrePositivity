module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraNonpositiveNativeInverseRoof
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraExtensionBaseChange

/-!
概要：元の非正次数逆 roof と左細分を、任意の後続段に沿って実 pullback する。
方針：元の塔の遷移の ofHom と既存 roof 合成を使う。
規約：元の両脚を保持し、分母の次数全射準同型性を実証する。使われ方：係数の共通底。
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

def refinementRoof : SurjectiveRoof R (Y.obj k) (X.obj i) :=
  SurjectiveRoof.comp R (SurjectiveRoof.ofHom R (Y.transition hm)) c.roof

def refinementProjection : (refinementRoof R c hm).apex ⟶ c.roof.apex :=
  MonoidPullback.snd (Y.transition hm) c.roof.denominator

lemma refinementRoof_denominator : (refinementRoof R c hm).denominator =
    MonoidPullback.fst (Y.transition hm) c.roof.denominator := Category.comp_id _

lemma refinementProjection_denominator :
    refinementProjection R c hm ≫ c.roof.denominator =
      (refinementRoof R c hm).denominator ≫ Y.transition hm := by
  rw [refinementRoof_denominator]
  exact (MonoidPullback.condition _ _).symm

lemma refinementProjection_numerator :
    refinementProjection R c hm ≫ c.roof.numerator =
      (refinementRoof R c hm).numerator := rfl

lemma refinementRoof_nonpositive [(Y.obj k).X.IsStrictlyLE 0] :
    (refinementRoof R c hm).apex.X.IsStrictlyLE 0 := by
  have := c.roof_nonpositive
  exact CochainPullback.isStrictlyLE (Y.transition hm).hom c.roof.denominator.hom 0

def refinementSource : Mon (Complex R) :=
  ExtensionBaseChange.algebra R (X.transition hm) c.sourceProjection

def refinementSourceProjection : refinementSource R c hm ⟶ X.obj k :=
  ExtensionBaseChange.base R (X.transition hm) c.sourceProjection

def refinementSourceUpper : refinementSource R c hm ⟶ c.source :=
  ExtensionBaseChange.upper R (X.transition hm) c.sourceProjection

lemma refinementSource_condition : refinementSourceProjection R c hm ≫ X.transition hm =
    refinementSourceUpper R c hm ≫ c.sourceProjection :=
  ExtensionBaseChange.condition R _ _

lemma refinementSourceProjection_epi : Epi (refinementSourceProjection R c hm).hom := by
  have := c.sourceProjection_epi
  exact ExtensionBaseChange.base_epi R _ _

lemma refinementSourceProjection_quasiIso :
    QuasiIso (refinementSourceProjection R c hm).hom := by
  have := c.sourceProjection_epi
  exact cochainPullback_fst_quasiIso _ _ c.sourceProjection_quasiIso

lemma refinementSource_nonpositive [(X.obj k).X.IsStrictlyLE 0] :
    (refinementSource R c hm).X.IsStrictlyLE 0 := by
  have := c.source_nonpositive
  exact ExtensionBaseChange.nonpositive R _ _

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.NonpositiveInverseRoof
