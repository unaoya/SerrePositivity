module

public import SerrePositivity.KST.Spectra.TracedOriginalLoopIntervalStructure
public import SerrePositivity.KST.Spectra.SequenceExactStageInterval
public import SerrePositivity.KST.Spectra.RawSpectrumStrictParameterHomotopy

/-!
概要：元の raw 源比較からトレース付き単位の射影への、同じ段区間を持つ全列区間。
方針：全 Hom から得た厳密構造等式を自由区間値の列射へ束ねる一般構成を使う。
規約：新たな充填や別の端点を選ばない。使われ方：実評価側の源区間の全列移送。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
namespace SerrePositivity.KST.Spectra.OmegaSpectrum
open RawSpectrumMapping

/-- 元の raw 源比較とトレース付き単位の射影の間の、同じ全列区間。 -/
def tracedOriginalLoopRawStrictInterval (X : OmegaSpectrum.{u}) :
    KanSequence.StrictInterval (tracedOriginalLoopRawComparison X)
      ((sequenceHom (tracedSignedLoopUnit X)).comp (signedLoopProjection X)) :=
  KanSequence.strictIntervalOfExactStagePaths X (KanSequence.signedLoopTail X.toKanSequence)
    (tracedOriginalLoopRawComparison X)
    ((sequenceHom (tracedSignedLoopUnit X)).comp (signedLoopProjection X))
    (tracedOriginalLoopRawComparison_level_interval X)
    (tracedOriginalLoop_level_interval_structure_path X)

/-- 全列区間の各段は、元の同じ源比較の段区間を自由区間値へ移したものそのもの。 -/
lemma tracedOriginalLoopRawStrictInterval_app (X : OmegaSpectrum.{u}) (n : ℕ) :
    (tracedOriginalLoopRawStrictInterval X).hom.app n =
      (tracedOriginalLoopRawComparison_level_interval X n).freeMap := rfl

/-- 同じ全列区間が与える、元の全 Hom 自身の実際の辺。 -/
def tracedOriginalLoopRawStrictInterval_edge (X : OmegaSpectrum.{u}) :
    (pointedSpace X (KanSequence.signedLoopTail X.toKanSequence)).right.Edge
      (PointedSimplicialSet.unitVertexEquiv _
        (homPoint X (KanSequence.signedLoopTail X.toKanSequence)
          (tracedOriginalLoopRawComparison X)))
      (PointedSimplicialSet.unitVertexEquiv _ (homPoint X
        (KanSequence.signedLoopTail X.toKanSequence)
        ((sequenceHom (tracedSignedLoopUnit X)).comp (signedLoopProjection X)))) :=
  strictIntervalEdge X (KanSequence.signedLoopTail X.toKanSequence)
    (tracedOriginalLoopRawStrictInterval X)

end SerrePositivity.KST.Spectra.OmegaSpectrum
