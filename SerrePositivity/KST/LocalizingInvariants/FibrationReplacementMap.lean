module

public import SerrePositivity.KST.LocalizingInvariants.MappingPathSequenceComparison
public import SerrePositivity.KST.LocalizingInvariants.CofibrantSpectrumLift
public import SerrePositivity.KST.Spectra.SpectrumFibrationReplacement

/-!
概要：任意の厳密 BF 正方形から、元の fibration 置換間の実 BF 射を構成する。
方針：mapping path 列の比較を単射置換へ持ち上げ、二つの射影との比較式を回収する。
規約：置換単位の厳密自然性は要求しない。使われ方：homotopy fiber の接続射の自然性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open SerrePositivity.KST.Spectra SerrePositivity.KST.Spectra.OmegaSpectrum
namespace SerrePositivity.KST.LocalizingInvariants.FibrationReplacementComparison
variable {X Y X' Y' : OmegaSpectrum.{u}} (p : X ⟶ Y) (q : X' ⟶ Y')
  (a : X ⟶ X') (b : Y ⟶ Y') (h : p ≫ b = a ≫ q)

def liftData : CofibrantSpectrumLift (fibrationReplacementComparison q)
    ((fibrationReplacementComparison p).comp (MappingPathComparison.map p q a b h)) :=
  cofibrantSpectrumLift (fibrationReplacementComparison q)
    (fun n => (KanSequence.replacementStage (fibrationPath q) n).projection_rlp)
    ((fibrationReplacementComparison p).comp (MappingPathComparison.map p q a b h))

def map : fibrationReplacement p ⟶ fibrationReplacement q := (liftData p q a b h).map

lemma map_comparison (n : ℕ) : (map p q a b h).app n ≫
    (fibrationReplacementComparison q).app n =
      (fibrationReplacementComparison p).app n ≫ (MappingPathComparison.map p q a b h).app n :=
  (liftData p q a b h).fac n

lemma map_projection : map p q a b h ≫ fibrationReplacementProjection q =
    fibrationReplacementProjection p ≫ b := by
  apply OmegaSpectrum.Hom.ext
  intro n
  change (map p q a b h).app n ≫ ((fibrationReplacementComparison q).app n ≫
      (KanSequence.mappingPathTarget (sequenceHom q)).app n) =
    ((fibrationReplacementComparison p).app n ≫
      (KanSequence.mappingPathTarget (sequenceHom p)).app n) ≫ b.app n
  rw [← Category.assoc, map_comparison, Category.assoc, MappingPathComparison.map_target,
    Category.assoc]

lemma map_retraction : map p q a b h ≫ fibrationReplacementRetraction q =
    fibrationReplacementRetraction p ≫ a := by
  apply OmegaSpectrum.Hom.ext
  intro n
  change (map p q a b h).app n ≫ ((fibrationReplacementComparison q).app n ≫
      (KanSequence.mappingPathSource (sequenceHom q)).app n) =
    ((fibrationReplacementComparison p).app n ≫
      (KanSequence.mappingPathSource (sequenceHom p)).app n) ≫ a.app n
  rw [← Category.assoc, map_comparison, Category.assoc, MappingPathComparison.map_source,
    Category.assoc]

end SerrePositivity.KST.LocalizingInvariants.FibrationReplacementComparison
