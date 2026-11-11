module

public import SerrePositivity.KST.Spectra.SpectrumCotensorPointedComparison
public import SerrePositivity.KST.Spectra.RawSpectrumPointedUnits
public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomTensorStrengthPoint
public import SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchangeVertices

/-!
概要：実際の BF cotensor の普遍評価と、それによる全 Hom 前合成を構成する。
方針：恒等射の比較像を uncurry し、豊穣自然性を恒等射へ制限する。
規約：元の比較射と厳密に一致する。別の写像空間同値を選ばない。
使われ方：cotensor と loop の coherent な比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Spectra.OmegaSpectrum

/-- 実際の BF cotensor の恒等射の像が表す普遍評価。 -/
def cotensorEvaluation (A : PointedSimplicialSet.{u}) (Y : OmegaSpectrum.{u}) :
    A ⟶ RawSpectrumMapping.pointedSpace (cotensor A Y) Y.toKanSequence :=
  uncurry' (RawSpectrumMapping.pointedIdentity (cotensor A Y) ≫
    cotensorPointedMappingComparison (cotensor A Y) Y A)

/-- 普遍評価は元の恒等射の比較像を表す。 -/
@[simp]
lemma curry'_cotensorEvaluation (A : PointedSimplicialSet.{u}) (Y : OmegaSpectrum.{u}) :
    curry' (cotensorEvaluation A Y) =
      RawSpectrumMapping.pointedIdentity (cotensor A Y) ≫
        cotensorPointedMappingComparison (cotensor A Y) Y A :=
  curry'_uncurry' _

/-- 普遍評価の各段は、元の BF 置換射影の二つの源を交換した評価。 -/
@[reassoc]
lemma cotensorEvaluation_evaluation (A : PointedSimplicialSet.{u})
    (Y : OmegaSpectrum.{u}) (n : ℕ) :
    cotensorEvaluation A Y ≫
        RawSpectrumMapping.pointedEvaluation (cotensor A Y) Y.toKanSequence n =
      curry ((β_ ((cotensor A Y).level n).space A).hom ≫
        uncurry ((cotensorProjection A Y).app n)) := by
  apply curry'_injective
  rw [← curry'_ihom_map, curry'_cotensorEvaluation]
  dsimp only [cotensorPointedMappingComparison]
  rw [Category.assoc, Category.assoc, RawSpectrumMapping.cotensorComparison_evaluation]
  dsimp only [RawSpectrumMapping.exchangeFamily]
  have hp := congrArg (fun f ↦
    (RawSpectrumMapping.pointedIdentity (cotensor A Y) ≫ f) ≫
      (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso ((cotensor A Y).level n).space A
        (Y.level n).space).hom)
    (RawSpectrumMapping.pointedPost_evaluation (cotensor A Y) (cotensorProjection A Y) n)
  apply hp.trans
  rw [← Category.assoc, RawSpectrumMapping.pointedIdentity_evaluation]
  let U := ((cotensor A Y).level n).space
  let V := (Y.level n).space
  let p : U ⟶ (ihom A).obj V := (cotensorProjection A Y).app n
  change (curry' (𝟙 U) ≫ (ihom U).map p) ≫ (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso U A V).hom =
    curry' (curry ((β_ U A).hom ≫ uncurry p))
  rw [curry'_ihom_map, Category.id_comp, _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchangeVertices.curry'_hom]

/-- 普遍評価に全 Hom パラメータで前合成する射。 -/
def cotensorEvaluationPrecomposition (X Y : OmegaSpectrum.{u})
    (A : PointedSimplicialSet.{u}) :
    RawSpectrumMapping.pointedSpace X (cotensor A Y).toKanSequence ⟶
      (ihom A).obj (RawSpectrumMapping.pointedSpace X Y.toKanSequence) :=
  curry ((β_ A (RawSpectrumMapping.pointedSpace X (cotensor A Y).toKanSequence)).hom ≫
    (RawSpectrumMapping.pointedSpace X (cotensor A Y).toKanSequence) ◁
      cotensorEvaluation A Y ≫ RawSpectrumMapping.pointedComposition X (cotensor A Y)
        Y.toKanSequence)

/-- 普遍評価による前合成は、元の BF cotensor 比較射そのもの。 -/
lemma cotensorEvaluationPrecomposition_eq (X Y : OmegaSpectrum.{u})
    (A : PointedSimplicialSet.{u}) :
    cotensorEvaluationPrecomposition X Y A = cotensorPointedMappingComparison X Y A := by
  let C := cotensor A Y
  let M := RawSpectrumMapping.pointedSpace X C.toKanSequence
  have h := congrArg (fun f ↦ (ρ_ M).inv ≫
    M ◁ RawSpectrumMapping.pointedIdentity C ≫ f)
    (cotensorPointedMappingComparison_composition X C Y A)
  simp only [id_tensorHom] at h
  have hu := congrArg (fun f ↦ f ≫ cotensorPointedMappingComparison X Y A)
    (RawSpectrumMapping.pointedComposition_identity X C)
  simp only [Category.assoc, Category.id_comp] at hu
  dsimp only [cotensorEvaluationPrecomposition]
  rw [← Category.assoc, curry_natural_right, ← _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomTensorStrengthPoint.point,
    curry'_cotensorEvaluation]
  simp only [whiskerLeft_comp, Category.assoc]
  exact h.symm.trans hu

/-- 普遍評価による前合成は実際の自明 Kan fibration。 -/
lemma cotensorEvaluationPrecomposition_trivialKanFibration (X Y : OmegaSpectrum.{u})
    (A : PointedSimplicialSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (cotensorEvaluationPrecomposition X Y A).right := by
  rw [cotensorEvaluationPrecomposition_eq]
  exact cotensorPointedMappingComparison_trivialKanFibration X Y A

end SerrePositivity.KST.Spectra.OmegaSpectrum
