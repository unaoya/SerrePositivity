module
public import SerrePositivity.KST.Fibration.DGNuBoundaryFamily
public import SerrePositivity.KST.Fibration.DGKPositiveEvaluation
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.SquareFunctorTransport

/-! # ν 像の元の S• 境界商四角形と、固定 K の実正段四角形

安定側の全 Hom 作用との厳密な照合を coherent nerve に送り、元の ν 像を回収する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v w
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction
open SerrePositivity.KST.LocalizingInvariants
open SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.Fibration

local instance nuBoundaryInfinitySpectrumCategory : SimplicialCategory OmegaSpectrum.{w} :=
  OmegaSpectrum.simplicialCategory

/-- 安定側の元の S• 境界商の全作用を、同じ Ex∞ Kan 値に送る。 -/
def stableSBoundaryKanEnrichedFunctor (r : ℕ) :
    EnrichedFunctor SSet.{w} _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{w} PointedKanObject.{w} :=
  (stableBoundaryPointedEnrichedFunctor r).comp SSet exInfinityPointedKanEnrichedFunctor

/-- 安定側 S• の元の境界商と全高次入力を持つ ∞ 関手。 -/
def stableSBoundaryKanInfinityFunctor (r : ℕ) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{w} ⟶ PointedKanInfinity.{w} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (stableSBoundaryKanEnrichedFunctor r)

variable (A : Type u) [CommRing A]

/-- 元の基点固定境界商関手は、同じ ν の後合成として全 Hom 上で一致する。 -/
theorem dgNuBoundaryPointedEnriched_eq (r : ℕ) :
    (presentedPerfectDGEnrichedExactFunctor A).comp SSet
        (stableBoundaryPointedEnrichedFunctor r) =
      presentedPerfectDGBoundaryPointedEnrichedFunctor A r := by
  apply EnrichedFunctor.ext SSet
  case h_obj => intro P; rfl
  case h_map =>
    intro P Q
    simp only [eqToHom_refl, Category.comp_id]
    exact dgNuBoundaryFamily_map A r P Q

/-- 同じ Kan 置換後も、元の全作用を保つ ν の後合成として一致する。 -/
theorem dgNuSBoundaryKanEnriched_eq (r : ℕ) :
    (presentedPerfectDGEnrichedExactFunctor A).comp SSet
        (stableSBoundaryKanEnrichedFunctor r) =
      presentedPerfectDGBoundaryKanEnrichedFunctor A r := by
  have h := congrArg (fun F => F.comp SSet exInfinityPointedKanEnrichedFunctor)
    (dgNuBoundaryPointedEnriched_eq A r)
  exact (enrichedFunctor_comp_assoc (presentedPerfectDGEnrichedExactFunctor A)
    (stableBoundaryPointedEnrichedFunctor r) exInfinityPointedKanEnrichedFunctor).symm.trans h

/-- 境界商の全入力 ∞ 図式は、元の ν の像に S• を適用した同じ全図式。 -/
theorem dgNuSBoundaryKanInfinity_eq (r : ℕ) :
    dgKInputNu A ≫ stableSBoundaryKanInfinityFunctor r =
      presentedPerfectDGBoundaryKanInfinityFunctor A r := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (presentedPerfectDGEnrichedExactFunctor A) ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (stableSBoundaryKanEnrichedFunctor r) = _
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap_comp, dgNuSBoundaryKanEnriched_eq]
  rfl

/-- ν 像の元の Verdier 四角形の S• 境界商を、同じ固定 K の実正段と全体で比較。 -/
def dgRelativeVerdierSBoundaryFixedKSquareIso (r : ℕ)
    (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.RelativeVerdierDiagram (dgKInputNu.{u, v} A)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (d.image.square ≫ stableSBoundaryKanInfinityFunctor r)
      (d.square ≫ dgKInputK A ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (spectrumKanEvaluation (r + 1))) := by
  have he : d.image.square ≫ stableSBoundaryKanInfinityFunctor r =
      d.square ≫ presentedPerfectDGBoundaryKanInfinityFunctor A r := by
    rw [← d.image_eq, Category.assoc, dgNuSBoundaryKanInfinity_eq]
  rw [he]
  exact dgRelativeSBoundaryFixedKSquareIso A r d

/-- 元の ν 像の S• 四角形の引き戻し性と、同じ K 正段四角形の引き戻し性は同値。 -/
theorem dgRelativeKPositiveSquare_isPullback_iff (r : ℕ)
    (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.RelativeVerdierDiagram (dgKInputNu.{u, v} A)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare (d.image.square ≫ stableSBoundaryKanInfinityFunctor r) ↔
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare
        (d.square ≫ dgKInputK A ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (spectrumKanEvaluation (r + 1))) :=
  ⟨fun h => h.of_functorIso (dgRelativeVerdierSBoundaryFixedKSquareIso A r d),
    fun h => h.of_functorIso (dgRelativeVerdierSBoundaryFixedKSquareIso A r d).symm⟩

end SerrePositivity.KST.Fibration
