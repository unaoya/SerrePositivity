module
public import SerrePositivity.KST.Fibration.PositiveKanEvaluationDetection
public import SerrePositivity.KST.Fibration.FiberSquareKanEvaluation
public import SerrePositivity.KST.Fibration.DGRelativeFiberComparison
public import SerrePositivity.KST.Fibration.DGNuSBoundaryInfinity
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SquareConePostcomp
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.RightFibrationMappingSpan

/-! # 元の相対 K 四角形の引き戻し性を、同じ正段・ν 像の S• 四角形で検出する -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v w
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories

open SerrePositivity.KST.SConstruction
open SerrePositivity.KST.LocalizingInvariants
open SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.Fibration

local instance relativePositiveSpectrumCategory : SimplicialCategory OmegaSpectrum.{w} :=
  OmegaSpectrum.simplicialCategory

variable (A : Type u) [CommRing A] (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.RelativeVerdierDiagram (dgKInputNu.{u, v} A))

/-- 同じ cospan の canonical fiber 錐は、各実段評価後にも極限錐となる。 -/
theorem dgRelativeKLimitCone_evaluation_isLimit (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone ((dgRelativeKLimitCone A d).postcomp
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (spectrumKanEvaluation n))) := by
  let s := dgRelativeCanonicalFiberSquare A d
  let t : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroTriangle Sp.{max (u + 1) v} := ⟨s.square, s.zero_corner⟩
  have h := spectrumFiberSquare_evaluation_isPullback t s.isPullback n
  have hc := (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.isLimitCone_map_pullbackCone_iff
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (spectrumKanEvaluation n)) s.square).mpr h
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.isLimitCone_iff_of_cone_val_eq _ _ ?_).mp hc
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.cospanConeSquareIso.hom ≫
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.cospanConeSquareIso.inv ≫ (dgRelativeKLimitCone A d).val)) ≫ _ = _
  simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  rfl

/-- 二つの評価錐が極限なら、同じ全錐比較を射影した評価辺は可逆。 -/
theorem dgRelativeFiberComparison_evaluation_isInvertible (n : ℕ)
    (h : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare ((d.square ≫ dgKInputK A) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (spectrumKanEvaluation n))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (X := PointedKanInfinity.{max (u + 1) v})
      ((dgRelativeFiberComparison A d).map
        ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (spectrumKanEvaluation n)))) := by
  let Q := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (spectrumKanEvaluation n)
  let p := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan (d.square ≫ dgKInputK A)
  let e := (dgRelativeFiberConeComparison A d).map
    ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverPostcomp p Q))
  have hc := (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.isLimitCone_map_pullbackCone_iff Q (d.square ≫ dgKInputK A)).mpr h
  have hd := dgRelativeKLimitCone_evaluation_isLimit A d n
  have he : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (X := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (p ≫ Q)) e :=
    isIso_of_isTerminal hc.isTerminalHo hd.isTerminalHo _
  have hp := he.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (p ≫ Q))
  have eqp := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.sliceOverPostcomp_projection p Q
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (X := PointedKanInfinity.{max (u + 1) v})
    ((dgRelativeFiberConeComparison A d).map
      ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection p ≫ Q)))
  rw [← eqp]
  exact hp

/-- 全正段での元の四角形の引き戻し性は、元の Sp 四角形へ反映される。 -/
theorem dgRelativeK_isPullback_of_positive_evaluation
    (h : ∀ r : ℕ, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare ((d.square ≫ dgKInputK A) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (spectrumKanEvaluation (r + 1)))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare (d.square ≫ dgKInputK A) := by
  apply (dgRelativeK_isPullback_iff_fiberComparison_isInvertible A d).mpr
  exact spectrumEdge_isInvertible_of_positive_evaluation
    (SSet.Edge.ofTruncated (dgRelativeFiberComparison A d))
    (fun r => dgRelativeFiberComparison_evaluation_isInvertible A d (r + 1) (h r))

/-- 相対 (d) は、ν 像の元の全正 S• 境界商四角形の引き戻し性と同値。 -/
theorem dgRelativeK_isPullback_iff_sBoundary :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare (d.square ≫ dgKInputK A) ↔
      ∀ r : ℕ, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare (d.image.square ≫ stableSBoundaryKanInfinityFunctor r) := by
  constructor
  · intro h r
    apply (dgRelativeKPositiveSquare_isPullback_iff A r d).mpr
    exact spectrumFiberSquare_evaluation_isPullback (dgRelativeKZeroTriangle A d) h (r + 1)
  · intro h
    apply dgRelativeK_isPullback_of_positive_evaluation A d
    intro r
    exact (dgRelativeKPositiveSquare_isPullback_iff A r d).mp (h r)

end SerrePositivity.KST.Fibration
