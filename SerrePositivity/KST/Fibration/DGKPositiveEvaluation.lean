module
public import SerrePositivity.KST.Fibration.DGKSBoundaryCoherentComparison

/-! # 固定 K の同じ正段評価と、元の相対四角形の全 S• 比較

元の BF 全 Hom の評価式で、前段の正段関手を K の後合成と厳密に照合する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v w
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction
open SerrePositivity.KST.LocalizingInvariants
open SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.Fibration

local instance positiveEvaluationSpectrumCategory : SimplicialCategory OmegaSpectrum.{w} :=
  OmegaSpectrum.simplicialCategory

/-- 同じ BF スペクトルの全高次 Hom を各段で評価する厳密豊穣関手。 -/
def spectrumKanEvaluation (n : ℕ) :
    EnrichedFunctor SSet.{w} OmegaSpectrum.{w} PointedKanObject.{w} where
  obj X := ⟨(X.level n).space, (show KanComplex (X.level n).space.right from inferInstance)⟩
  map X Y := OmegaSpectrum.evaluation X Y n
  map_id X := OmegaSpectrum.mappingIdentity_evaluation X n
  map_comp X Y Z := OmegaSpectrum.mappingComposition_evaluation X Y Z n

variable (A : Type u) [CommRing A]

/-- 正段の全 Hom 関手は、固定 BF 関手の同じ段での評価に厳密に一致。 -/
theorem dgKPositiveKanEnrichedFunctor_eq_evaluation (r : ℕ) :
    (presentedPerfectDGBFEnrichedFunctor A).comp SSet (spectrumKanEvaluation (r + 1)) =
      dgKPositiveKanEnrichedFunctor A r := by
  apply EnrichedFunctor.ext SSet
  case h_obj =>
    intro P
    rfl
  case h_map =>
    intro P Q
    simp only [eqToHom_refl, Category.comp_id]
    exact presentedPerfectDGBFEnrichedFunctor_evaluation A P Q (r + 1)

/-- 元の正段 ∞ 関手は、同じ固定 K の後合成である。 -/
theorem dgKPositiveKanInfinity_eq_evaluation (r : ℕ) :
    dgKInputK A ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (spectrumKanEvaluation (r + 1)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (dgKPositiveKanEnrichedFunctor A r) := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (presentedPerfectDGBFEnrichedFunctor A) ≫ _ = _
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap_comp, dgKPositiveKanEnrichedFunctor_eq_evaluation]

/-- 元の固定 K を実正段で評価した全図式と、元の S• 境界商の全図式との自然同型。 -/
def dgKSBoundaryFixedKPositiveIso (r : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (presentedPerfectDGBoundaryKanInfinityFunctor A r)
      (dgKInputK A ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (spectrumKanEvaluation (r + 1))) :=
  (dgKPositiveKanInfinity_eq_evaluation A r).symm ▸ dgKSBoundaryPositiveIso A r

/-- 元の相対 K 四角形の評価と、元の相対 S• 境界商四角形の全 coherent 比較。 -/
def dgRelativeSBoundaryFixedKSquareIso (r : ℕ)
    (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.RelativeVerdierDiagram (dgKInputNu.{u, v} A)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (d.square ≫ presentedPerfectDGBoundaryKanInfinityFunctor A r)
      (d.square ≫ dgKInputK A ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (spectrumKanEvaluation (r + 1))) :=
  (dgKSBoundaryFixedKPositiveIso A r).precomp d.square

end SerrePositivity.KST.Fibration
