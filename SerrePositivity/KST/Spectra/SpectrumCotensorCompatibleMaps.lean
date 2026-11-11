module

public import SerrePositivity.KST.Spectra.SpectrumCotensorEvaluation
public import SerrePositivity.KST.Spectra.PullbackKanSequence

/-!
概要：普遍評価と厳密に可換な、元の射と cotensor の射の組の空間。
方針：普遍評価への前合成の自明 Kan fibration を、評価への後合成に沿い引き戻す。
規約：全 Hom パラメータを扱う。選んだ cotensorPost に関手法則を要求しない。
使われ方：coherent な cotensor 関手の写像空間。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories
open SSet.modelCategoryQuillen
namespace SerrePositivity.KST.Spectra.OmegaSpectrum.CotensorCompatible

/-- 元の Hom の全パラメータを普遍評価に後合成する。 -/
def evaluationPost (A : PointedSimplicialSet.{u}) (X Y : OmegaSpectrum.{u}) :
    RawSpectrumMapping.pointedSpace X Y.toKanSequence ⟶
      (ihom A).obj (RawSpectrumMapping.pointedSpace (cotensor A X) Y.toKanSequence) :=
  curry (cotensorEvaluation A X ▷ RawSpectrumMapping.pointedSpace X Y.toKanSequence ≫
    RawSpectrumMapping.pointedComposition (cotensor A X) X Y.toKanSequence)

/-- 元の射と cotensor の射が普遍評価と可換な組の点つき空間。 -/
def pointedSpace (A : PointedSimplicialSet.{u}) (X Y : OmegaSpectrum.{u}) :
    PointedSimplicialSet.{u} :=
  pullback (cotensorEvaluationPrecomposition (cotensor A X) Y A) (evaluationPost A X Y)

/-- 組から cotensor の射を取り出す。 -/
def cotensorMap (A : PointedSimplicialSet.{u}) (X Y : OmegaSpectrum.{u}) :
    pointedSpace A X Y ⟶
      RawSpectrumMapping.pointedSpace (cotensor A X) (cotensor A Y).toKanSequence :=
  pullback.fst _ _

/-- 組から元の射を取り出す。 -/
def sourceMap (A : PointedSimplicialSet.{u}) (X Y : OmegaSpectrum.{u}) :
    pointedSpace A X Y ⟶ RawSpectrumMapping.pointedSpace X Y.toKanSequence :=
  pullback.snd _ _

/-- 二つの射影は普遍評価と厳密に可換。 -/
@[reassoc]
lemma condition (A : PointedSimplicialSet.{u}) (X Y : OmegaSpectrum.{u}) :
    cotensorMap A X Y ≫ cotensorEvaluationPrecomposition (cotensor A X) Y A =
      sourceMap A X Y ≫ evaluationPost A X Y :=
  pullback.condition

/-- 可換な組の空間の元の射への射影は実際の自明 Kan fibration。 -/
lemma sourceMap_trivialKanFibration (A : PointedSimplicialSet.{u})
    (X Y : OmegaSpectrum.{u}) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (sourceMap A X Y).right := by
  exact ⟨_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedPullback_snd_rlp _ _
    (cotensorEvaluationPrecomposition_trivialKanFibration (cotensor A X) Y A).mem⟩

/-- 可換な組の全空間は Kan。 -/
instance pointedSpace_kanComplex (A : PointedSimplicialSet.{u})
    (X Y : OmegaSpectrum.{u}) : KanComplex (pointedSpace A X Y).right := by
  let compatibleComparisonTrivial :
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (cotensorEvaluationPrecomposition (cotensor A X) Y A).right :=
    cotensorEvaluationPrecomposition_trivialKanFibration (cotensor A X) Y A
  let compatibleComparisonFibration : HomotopicalAlgebra.Fibration
      (cotensorEvaluationPrecomposition (cotensor A X) Y A).right :=
    (modelCategoryQuillen.fibration_iff _).2 (fun _ _ j hj ↦
      compatibleComparisonTrivial.mem j (modelCategoryQuillen.J_le_monomorphisms j hj))
  exact @_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedPullback_kanComplex _ _ _
    (cotensorEvaluationPrecomposition (cotensor A X) Y A) (evaluationPost A X Y)
    compatibleComparisonFibration (RawSpectrumMapping.pointedSpace_kanComplex X Y.toKanSequence)

/-- 元の Hom への実際の射影を順射とする同値。 -/
def sourceEquivalence (A : PointedSimplicialSet.{u}) (X Y : OmegaSpectrum.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence (pointedSpace A X Y).right (mappingSpace X Y) := by
  letI compatibleProjectionTrivial : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (sourceMap A X Y).right :=
    sourceMap_trivialKanFibration A X Y
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.qCatEquivalenceOfTrivialKanFibration (sourceMap A X Y).right

/-- 同値の順写像は元の射への射影そのもの。 -/
lemma sourceEquivalence_hom (A : PointedSimplicialSet.{u}) (X Y : OmegaSpectrum.{u}) :
    (sourceEquivalence A X Y).hom = (sourceMap A X Y).right := rfl

end SerrePositivity.KST.Spectra.OmegaSpectrum.CotensorCompatible
