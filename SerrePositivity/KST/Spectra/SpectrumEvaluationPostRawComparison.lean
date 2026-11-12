module

public import SerrePositivity.KST.Spectra.SpectrumEvaluationPostCoordinates
public import SerrePositivity.KST.Spectra.RawSpectrumCotensorIso
public import SerrePositivity.KST.Spectra.KanEquivalenceBridge

/-!
概要：元の evaluationPost を同じ厳密な cotensor 交換で戻し、BF 射影後の可換族へ同定する。
方針：可換組の普遍評価条件へ元の全 Hom 同型の逆を後合成する。
規約：全 Hom の射の厳密等式。使われ方：符号付き一段移動の元の評価写像への接続。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.KST.Spectra.OmegaSpectrum.CotensorCompatible
open RawSpectrumMapping

local instance rawEvaluationPostKan (K : PointedSimplicialSet.{u})
    (X Y : OmegaSpectrum.{u}) :
    KanComplex ((ihom K).obj (RawSpectrumMapping.pointedSpace
      (cotensor K X) Y.toKanSequence)).right := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.basedHom_kanComplex _ _

/-- 元の普遍評価写像を、同じ置換前 cotensor 値の全 Hom へ厳密同型で戻す。 -/
def rawEvaluationPost (K : PointedSimplicialSet.{u}) (X Y : OmegaSpectrum.{u}) :
    RawSpectrumMapping.pointedSpace X Y.toKanSequence ⟶
      RawSpectrumMapping.pointedSpace (cotensor K X) (KanSequence.mapping K Y.toKanSequence) :=
  evaluationPost K X Y ≫ cotensorInverse (cotensor K X) Y.toKanSequence K

/-- 元の評価写像の π 同型性は、同じ写像を厳密同型で戻したものと同値。 -/
lemma rawEvaluationPost_piIsomorphism_iff (K : PointedSimplicialSet.{u})
    (X Y : OmegaSpectrum.{u}) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (rawEvaluationPost K X Y).right ↔
      _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (evaluationPost K X Y).right := by
  let e : ((ihom K).obj
      (RawSpectrumMapping.pointedSpace (cotensor K X) Y.toKanSequence)).right ≅
      (RawSpectrumMapping.pointedSpace (cotensor K X)
        (KanSequence.mapping K Y.toKanSequence)).right :=
    PointedSimplicialSet.forget.mapIso (cotensorIso (cotensor K X) Y.toKanSequence K).symm
  have hi := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanPiIsomorphism.of_iso e
  constructor
  · intro h
    exact _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism.of_comp h hi
  · intro h
    exact h.comp hi

/-- 可換な射の空間の BF 射影は、元の evaluationPost を通る同じ全 Hom 写像。 -/
@[reassoc]
lemma cotensorMap_projection (K : PointedSimplicialSet.{u}) (X Y : OmegaSpectrum.{u}) :
    cotensorMap K X Y ≫ pointedPost (cotensor K X) (cotensorProjection K Y) =
      sourceMap K X Y ≫ rawEvaluationPost K X Y := by
  have h := congrArg (· ≫ cotensorInverse (cotensor K X) Y.toKanSequence K) (condition K X Y)
  rw [cotensorEvaluationPrecomposition_eq, cotensorPointedMappingComparison,
    Category.assoc, Category.assoc, cotensorComparison_inverse, Category.comp_id] at h
  exact h

/-- 元の評価を戻した同じ全 Hom の段座標は、元の評価座標の逆交換。 -/
lemma rawEvaluationPost_evaluation (K : PointedSimplicialSet.{u})
    (X Y : OmegaSpectrum.{u}) (n : ℕ) :
    rawEvaluationPost K X Y ≫
      pointedEvaluation (cotensor K X) (KanSequence.mapping K Y.toKanSequence) n =
    pointedEvaluation X Y.toKanSequence n ≫ evaluationPostAt K X Y n ≫
      (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso ((cotensor K X).level n).space K (Y.level n).space).inv := by
  rw [rawEvaluationPost, Category.assoc, cotensorInverse_evaluation]
  dsimp only [inverseExchangeFamily]
  rw [← Category.assoc, evaluationPost_evaluation, Category.assoc]
  rfl

end SerrePositivity.KST.Spectra.OmegaSpectrum.CotensorCompatible
