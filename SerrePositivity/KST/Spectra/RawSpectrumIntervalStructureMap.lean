module

public import SerrePositivity.KST.Spectra.RawSpectrumIntervalStructure
public import SerrePositivity.KST.Spectra.PointedIntervalNaturality

/-!
概要：全 Hom 区間の段評価を転置し、同じ列射へ後合成した区間も厳密な構造条件を満たす。
方針：元の全 Hom 区間の構造等式と、列射の実区間上の厳密自然性を合成する。
規約：全ての次数・一般の Kan 標的。使われ方：源単位区間を単位で評価した構造条件。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalClosed
namespace SerrePositivity.KST.Spectra.RawSpectrumMapping
variable (X : OmegaSpectrum.{u}) (Y Z : KanSequence.{u}) {T : PointedSimplicialSet.{u}}
  {f g : T ⟶ pointedSpace X Y}
  (P : PointedMapping.VerticalPath (PointedObject.toPoint (pointedSpace X Y)) f g)
  (p : KanSequence.Hom (KanSequence.mapping T Y) Z)

/-- 同じ全 Hom 区間の転置した段評価を、指定した列射へ後合成する。 -/
def pointedInterval_mappedStage (n : ℕ) :
    PointedMapping.VerticalPath (PointedObject.toPoint (Z.level n).space)
      (PointedMapping.transpose (f ≫ pointedEvaluation X Y n) ≫ p.app n)
      (PointedMapping.transpose (g ≫ pointedEvaluation X Y n) ≫ p.app n) :=
  ((P.basedPost (pointedEvaluation X Y n)).basedTranspose).basedPost (p.app n)

/-- 元の同じ全 Hom 区間と列射から来る段区間は、構造経路が区間全体で厳密一致する。 -/
lemma pointedInterval_mappedStage_condition (n : ℕ) :
    ((pointedInterval_mappedStage X Y Z P p (n + 1)).pre (X.sigma n)).path =
      ((pointedInterval_mappedStage X Y Z P p n).suspension.forgetProjection.basedPost
        (Z.sigma n)).path := by
  have hpre := PointedMapping.VerticalPath.pre_basedPost_path
    (P.basedPost (pointedEvaluation X Y (n + 1))).basedTranspose (X.sigma n) (p.app (n + 1))
  have hstep := PointedMapping.VerticalPath.basedPost_sequence_step_path p n
    (P.basedPost (pointedEvaluation X Y n)).basedTranspose
  have h := pointedInterval_transposed_condition X Y P n
  have ht := congrArg (· ≫ ((ihom (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (X.level n).space)).map (p.app (n + 1))).right) h
  exact hpre.trans (ht.trans hstep.symm)

end SerrePositivity.KST.Spectra.RawSpectrumMapping
