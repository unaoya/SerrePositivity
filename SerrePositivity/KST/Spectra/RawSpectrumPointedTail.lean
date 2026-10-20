module

public import SerrePositivity.KST.Spectra.RawSpectrumMappingFunctor
public import SerrePositivity.KST.Spectra.RawSpectrumPointedPreComposition
public import SerrePositivity.KST.Spectra.SpectrumTailEnriched
public import SerrePositivity.KST.Spectra.ShiftedKanSequence

/-!
概要：BF 源と一般の Kan 列の元の点つき Hom を、零段を忘れる同じ射で移す。
方針：一段先の同じ評価族を整合写像空間へ持ち上げる。
規約：全 Hom の自然な射。使われ方：元の evaluationPost の一段移動への接続。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory SSet
namespace SerrePositivity.KST.Spectra.RawSpectrumMapping

/-- 元の点つき整合 Hom の零段を忘れる射。標的の構造単射は不要。 -/
def pointedTail (X : OmegaSpectrum.{u}) (Y : KanSequence.{u}) :
    pointedSpace X Y ⟶ pointedSpace (OmegaSpectrum.tail X) Y.tail :=
  pointedLift (OmegaSpectrum.tail X) Y.tail (fun n => pointedEvaluation X Y (n + 1))
    (fun n => congrArg Under.Hom.right (pointedEvaluation_condition X Y (n + 1)))

/-- 一段移動後の各段は、同じ一段先の元の評価。 -/
@[reassoc]
lemma pointedTail_evaluation (X : OmegaSpectrum.{u}) (Y : KanSequence.{u}) (n : ℕ) :
    pointedTail X Y ≫ pointedEvaluation (OmegaSpectrum.tail X) Y.tail n =
      pointedEvaluation X Y (n + 1) := pointedLift_evaluation _ _ _ _ _

/-- 一段移動は、一般の Kan 列の後合成と全 Hom で厳密に可換。 -/
@[reassoc]
lemma pointedTail_post (X : OmegaSpectrum.{u}) {Y Z : KanSequence.{u}}
    (p : KanSequence.Hom Y Z) :
    pointedPost X p ≫ pointedTail X Z =
      pointedTail X Y ≫ pointedPost (OmegaSpectrum.tail X) (KanSequence.tailHom p) := by
  apply pointed_hom_ext (OmegaSpectrum.tail X) Z.tail
  intro n
  rw [Category.assoc, pointedTail_evaluation, pointedPost_evaluation,
    Category.assoc, pointedPost_evaluation, ← Category.assoc, pointedTail_evaluation]
  rfl

/-- BF 標的では、同じ元の一段移動は既存の豊穣 Hom の一段移動そのもの。 -/
lemma pointedTail_BF_right (X Y : OmegaSpectrum.{u}) :
    (pointedTail X Y.toKanSequence).right = OmegaSpectrum.tailMapping X Y := rfl

end SerrePositivity.KST.Spectra.RawSpectrumMapping
