module

public import SerrePositivity.InfinityCategories.F2.Ind.SectionProductWeightedBase
public import SerrePositivity.InfinityCategories.F1.Scaffold.LeftScaffold

/-!
概要：全単体の切断の大域評価を、元の共同 weighted fibration の同じ初頂点引き戻しへ写す。
方針：元の大域評価と元の replacement 射影を、証明済みの底上の等式で引き戻しへ束ねる。
規約：元の両射影を保持する。同値性は後続の同じ fiber 比較で検出する。
使われ方：全単体上の分類比較に使う left scaffold の元の射。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.F2.Ind
variable {I : Type u} [Category.{u} I] {B : SSet.{u}} (F : I ⥤ LeftFibrationObject B)

instance sectionProductWeightedPullback_leftFibration :
    LeftFibration (pullback.snd (leftFibrationWeightedProjection F) (sectionProductBaseMap I B)) :=
  ⟨leftFibrations.pullback_snd _ _ (LeftFibration.mem (p := leftFibrationWeightedProjection F))⟩

/-- 同じ初頂点引き戻しへの、全単体の相対切断の元の大域評価射。 -/
def sectionProductScaffold :
    simplicialReplacement (strictLeftTransportSectionDiagram F ⋙ kanObjectForget) ⟶
      pullback (leftFibrationWeightedProjection F) (sectionProductBaseMap I B) :=
  pullback.lift (sectionProductWeightedEvaluation F)
    (simplicialReplacementProjection (strictLeftTransportSectionDiagram F ⋙ kanObjectForget))
    (sectionProductWeightedEvaluation_over_product F)

/-- 元の添字の積への射影は、同じ replacement の射影そのもの。 -/
lemma sectionProductScaffold_projection :
    sectionProductScaffold F ≫ pullback.snd _ _ =
      simplicialReplacementProjection (strictLeftTransportSectionDiagram F ⋙ kanObjectForget) :=
  pullback.lift_snd _ _ _

/-- 元の共同 weighted 全空間への射影は、構成済みの同じ大域評価射。 -/
lemma sectionProductScaffold_total : sectionProductScaffold F ≫ pullback.fst _ _ =
    sectionProductWeightedEvaluation F := pullback.lift_fst _ _ _

end SerrePositivity.InfinityCategories.F2.Ind
