module

public import SerrePositivity.KST.Spectra.SpectrumTracedSourceActionCoordinates
public import SerrePositivity.KST.Spectra.RawSpectrumIntervalStructure

/-!
概要：全列作用で回収した区間の始点を、元の実評価自身へ厳密に戻す。
方針：元の段評価で証明した全 Hom 等式で端点だけを付け替え、同じ実区間を使う。
規約：新しいホモトピーを選ばない。使われ方：実評価側の厳密な構造正方形。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.KST.Spectra.RawSpectrumMapping
variable (X Y : OmegaSpectrum.{u}) {A : PointedSimplicialSet.{u}}
  (φ : A ⟶ pointedSpace X Y.toKanSequence)

/-- 元の実評価自身から、同じ入力のトレース付き源単位作用へ至る全 Hom ホモトピー。 -/
def tracedActualSourceHomotopy :
    SSet.Homotopy
      (φ ≫ OmegaSpectrum.CotensorCompatible.signedEvaluationAt X Y
        (OmegaSpectrum.tracedOriginalLoopModelMap X)).right
      (tracedSourceUnitFamily X Y φ).right where
  h := (tracedSourceActionHomotopy X Y φ).h
  h₀ := (tracedSourceActionHomotopy X Y φ).h₀.trans
    (congrArg Under.Hom.right (tracedSourceActionParameterFamily X Y φ))
  h₁ := (tracedSourceActionHomotopy X Y φ).h₁
  rel := (tracedSourceActionHomotopy X Y φ).rel

/-- 同じ元の全列区間を回収したホモトピーは、元の零 Hom の基点を全区間で固定。 -/
lemma tracedActualSourceHomotopy_base :
    A.hom ▷ (Δ[1] : SSet.{u}) ≫ (tracedActualSourceHomotopy X Y φ).h =
      toUnit (𝟙_ SSet.{u} ⊗ (Δ[1] : SSet.{u})) ≫
        (pointedSpace X (KanSequence.signedLoopTail Y.toKanSequence)).hom :=
  tracedSourceActionHomotopy_base X Y φ

/-- 元の実評価を始点とする同じ全 Hom の区間を、点つき区間として表示。 -/
def tracedActualSourceInterval :
    PointedMapping.VerticalPath
      (PointedObject.toPoint (pointedSpace X (KanSequence.signedLoopTail Y.toKanSequence)))
      (φ ≫ OmegaSpectrum.CotensorCompatible.signedEvaluationAt X Y
        (OmegaSpectrum.tracedOriginalLoopModelMap X))
      (tracedSourceUnitFamily X Y φ) :=
  PointedMapping.VerticalPath.ofHomotopy (tracedActualSourceHomotopy X Y φ)
    (tracedActualSourceHomotopy_base X Y φ) (toUnit_unique _ _)

/-- 実評価側の新しい段区間は、同じ元の全 Hom 区間の段評価。 -/
def tracedActualSourceStageInterval (n : ℕ) :=
  (tracedActualSourceInterval X Y φ).basedPost
    (pointedEvaluation X (KanSequence.signedLoopTail Y.toKanSequence) n)

/-- 同じ実評価側の段区間は、二つの構造経路が辺全体で厳密に一致する。 -/
lemma tracedActualSourceStageInterval_condition (n : ℕ) :
    ((tracedActualSourceStageInterval X Y φ (n + 1)).basedPost
      (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (X.sigma n)
        ((KanSequence.signedLoopTail Y.toKanSequence).level (n + 1)).space)).path =
    ((tracedActualSourceStageInterval X Y φ n).basedPost
      (pointedStep X (KanSequence.signedLoopTail Y.toKanSequence) n)).path :=
  pointedInterval_evaluation_condition X (KanSequence.signedLoopTail Y.toKanSequence)
    (tracedActualSourceInterval X Y φ) n

/-- 転置した段区間の源制限と列の構造像も、同じ辺として厳密一致する。 -/
lemma tracedActualSourceStageInterval_transposed_condition (n : ℕ) :
    (((tracedActualSourceStageInterval X Y φ (n + 1)).basedTranspose).pre (X.sigma n)).path =
    (PointedMapping.VerticalPath.basedPost
      (tracedActualSourceStageInterval X Y φ n).basedTranspose.suspension.forgetProjection
      ((KanSequence.mapping A (KanSequence.signedLoopTail Y.toKanSequence)).sigma n)).path :=
  pointedInterval_transposed_condition X (KanSequence.signedLoopTail Y.toKanSequence)
    (tracedActualSourceInterval X Y φ) n

end SerrePositivity.KST.Spectra.RawSpectrumMapping
