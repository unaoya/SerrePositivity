module
public import SerrePositivity.KST.NonConnective.DGKappaNativeBFZero
public import SerrePositivity.KST.Fibration.DGRelativeSpaceDetection

/-!
概要：同じ未完備 BF 四角形の元の実 fiber 比較を構成する。
方針：新 coherent 右辺・上辺の同じ cospan の実極限錐と全錐を比較し、全正段の検出を消費する。
規約：有限 BF 供給命題に条件付き。一般 BF 整流や別の固定 K は導入しない。
使われ方：K-6 の全 S• 比較から K-7 の同じ cone の構造辺への接続。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories

open SerrePositivity.KST.SConstruction SerrePositivity.KST.Spectra
open SerrePositivity.KST.LocalizingInvariants SerrePositivity.KST.Fibration
namespace SerrePositivity.KST.NonConnective
local instance nativeBFFiberSpectrumCategory : SimplicialCategory OmegaSpectrum.{w} :=
  OmegaSpectrum.simplicialCategory
variable (R : Type u) [CommRing R] (D : PerfDGInput.{u, max (u + 1) v} R)
  {κ : Cardinal.{u}} (I : DGKappaConeInput R D κ)
  (hBF : dgKappaNativeBFSquareComparison R D I)

/-- 概要：元の K 四角形の右辺と上辺をそのまま底とする、Sp の構成済み極限錐。
方針：同じ未完備 BF 四角形と元の錐比較へ既存の判定を適用する。
規約：有限 BF 供給命題に条件付き。旧 BF 右辺の fiber や固定 K の引き戻し性は主張しない。
使われ方：同じ実 cone の構造辺へ渡す元の実 fiber 比較。 -/
def dgKappaNativeBFKLimitCone : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan (dgKappaNativeBFSquare R D I hBF)) :=
  OmegaSpectrum.CoherentPullback.infinityCone _

theorem dgKappaNativeBFKLimitCone_isLimit : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (dgKappaNativeBFKLimitCone R D I hBF) :=
  OmegaSpectrum.CoherentPullback.infinityCone_isLimit _

/-- 概要：元の零角と右辺を変えず、左下の頂点を実 fiber に置き換えた四角形。
方針：同じ未完備 BF 四角形と元の錐比較へ既存の判定を適用する。
規約：有限 BF 供給命題に条件付き。固定 K の完備化後の引き戻し性は主張しない。
使われ方：同じ実 cone の構造辺へ渡す元の実 fiber 比較。 -/
def dgKappaNativeBFCanonicalFiberSquare : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.FiberSquare
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareRightArrow (dgKappaNativeBFSquare R D I hBF)) where
  square := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.coneSquare (dgKappaNativeBFKLimitCone R D I hBF)
  zero_corner := by
    have ht : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareTopEdge ≫ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.coneSquare (dgKappaNativeBFKLimitCone R D I hBF) =
        _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareTopEdge ≫ (dgKappaNativeBFSquare R D I hBF) := by
      rw [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.coneSquare_top]
      exact congrArg (fun q => q ≫ (dgKappaNativeBFSquare R D I hBF))
        _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.cospanSquareBoundary_topEdge
    have hz : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.coneSquare (dgKappaNativeBFKLimitCone R D I hBF)) 0 1 =
        _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex (dgKappaNativeBFSquare R D I hBF) 0 1 := by
      rw [← _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareTopEdge_source, ht, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareTopEdge_source]
    rw [hz]
    exact dgKappaNativeBFSquare_zero_corner R D I hBF
  right_edge := by
    rw [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.coneSquare_right]
    change horn₂₂.ι₀₂ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan (dgKappaNativeBFSquare R D I hBF) = _
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.cospanSquareBoundary_rightEdge]
    rw [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareRightArrow_edge]
    exact (SSet.yonedaEquiv.symm_apply_apply
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫ (dgKappaNativeBFSquare R D I hBF))).symm
  isPullback := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.coneSquare_isPullback _ (dgKappaNativeBFKLimitCone_isLimit R D I hBF)

/-- 概要：比較元は元の K 四角形の全錐、比較先は同じ cospan の実極限錐。
方針：同じ未完備 BF 四角形と元の錐比較へ既存の判定を適用する。
規約：有限 BF 供給命題に条件付き。固定 K の完備化後の引き戻し性は主張しない。
使われ方：同じ実 cone の構造辺へ渡す元の実 fiber 比較。 -/
def dgKappaNativeBFFiberConeComparison :
    SSet.Truncated.Edge (X := (truncation 2).obj
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan (dgKappaNativeBFSquare R D I hBF))))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCone (dgKappaNativeBFSquare R D I hBF)) (dgKappaNativeBFKLimitCone R D I hBF) :=
  Classical.choice ((dgKappaNativeBFKLimitCone_isLimit R D I hBF).nonempty_edge _)

/-- 概要：全錐の同じ比較を頂点へ射影した、元の K 頂点から実 fiber への辺。
方針：同じ未完備 BF 四角形と元の錐比較へ既存の判定を適用する。
規約：有限 BF 供給命題に条件付き。固定 K の完備化後の引き戻し性は主張しない。
使われ方：同じ実 cone の構造辺へ渡す元の実 fiber 比較。 -/
def dgKappaNativeBFFiberComparison :
    SSet.Truncated.Edge (X := (truncation 2).obj Sp.{max (u + 1) v})
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCone (dgKappaNativeBFSquare R D I hBF)).vertex (dgKappaNativeBFKLimitCone R D I hBF).vertex :=
  (dgKappaNativeBFFiberConeComparison R D I hBF).map ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection _))

/-- 概要：同じ比較辺と、比較元・比較先の各元の脚の実合成三角形。
方針：同じ未完備 BF 四角形と元の錐比較へ既存の判定を適用する。
規約：有限 BF 供給命題に条件付き。固定 K の完備化後の引き戻し性は主張しない。
使われ方：同じ実 cone の構造辺へ渡す元の実 fiber 比較。 -/
def dgKappaNativeBFFiberComparisonLegTriangle
    (k : (horn 2 2 : SSet.{max (u + 1) v + 1}) _⦋0⦌) :
    SSet.Truncated.Edge.CompStruct (dgKappaNativeBFFiberComparison R D I hBF)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.nativeConeLeg (dgKappaNativeBFKLimitCone R D I hBF) k)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.nativeConeLeg (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCone (dgKappaNativeBFSquare R D I hBF)) k) :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.nativeConeComparisonLegTriangle (dgKappaNativeBFFiberConeComparison R D I hBF) k

/-- 概要：元の相対 K 四角形が引き戻しとなる必要十分条件は、同じ実比較辺の可逆性。
方針：同じ未完備 BF 四角形と元の錐比較へ既存の判定を適用する。
規約：有限 BF 供給命題に条件付き。固定 K の完備化後の引き戻し性は主張しない。
使われ方：同じ実 cone の構造辺へ渡す元の実 fiber 比較。 -/
theorem dgKappaNativeBFK_isPullback_iff_fiberComparison_isInvertible :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare (dgKappaNativeBFSquare R D I hBF) ↔
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (X := Sp.{max (u + 1) v}) (dgKappaNativeBFFiberComparison R D I hBF) := by
  constructor
  · intro h
    have : IsIso (Truncated.HomotopyCategory.homMk
        (dgKappaNativeBFFiberConeComparison R D I hBF)) :=
      isIso_of_isTerminal h.isTerminalHo (dgKappaNativeBFKLimitCone_isLimit R D I hBF).isTerminalHo _
    change IsIso ((hoFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection _)).toFunctor.map
      (Truncated.HomotopyCategory.homMk (dgKappaNativeBFFiberConeComparison R D I hBF)))
    infer_instance
  · intro h
    have he : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (X := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan (dgKappaNativeBFSquare R D I hBF))) (dgKappaNativeBFFiberConeComparison R D I hBF) :=
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.rightFibration_reflects_isInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection _)
        (SSet.Edge.ofTruncated (dgKappaNativeBFFiberConeComparison R D I hBF)) h
    have : IsIso (Truncated.HomotopyCategory.homMk
        (dgKappaNativeBFFiberConeComparison R D I hBF)) := he
    exact (dgKappaNativeBFKLimitCone_isLimit R D I hBF).of_vertexIso
      (asIso (Truncated.HomotopyCategory.homMk (dgKappaNativeBFFiberConeComparison R D I hBF))).symm


/-- 概要：同じ cospan の canonical fiber 錐は、各実段評価後にも極限錐となる。
方針：同じ未完備 BF 四角形と元の錐比較へ既存の判定を適用する。
規約：有限 BF 供給命題に条件付き。固定 K の完備化後の引き戻し性は主張しない。
使われ方：同じ実 cone の構造辺へ渡す元の実 fiber 比較。 -/
theorem dgKappaNativeBFKLimitCone_spaceEvaluation_isLimit (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone ((dgKappaNativeBFKLimitCone R D I hBF).postcomp
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (spectrumSpaceEvaluation n))) := by
  let s := dgKappaNativeBFCanonicalFiberSquare R D I hBF
  let t : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.ZeroTriangle Sp.{max (u + 1) v} := ⟨s.square, s.zero_corner⟩
  have h := spectrumFiberSquare_spaceEvaluation_isPullback t s.isPullback n
  have hc := (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.isLimitCone_map_pullbackCone_iff
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (spectrumSpaceEvaluation n)) s.square).mpr h
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.isLimitCone_iff_of_cone_val_eq _ _ ?_).mp hc
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.cospanConeSquareIso.hom ≫
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.cospanConeSquareIso.inv ≫ (dgKappaNativeBFKLimitCone R D I hBF).val)) ≫ _ = _
  simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  rfl

/-- 概要：二つの評価錐が極限なら、同じ全錐比較を射影した評価辺は可逆。
方針：同じ未完備 BF 四角形と元の錐比較へ既存の判定を適用する。
規約：有限 BF 供給命題に条件付き。固定 K の完備化後の引き戻し性は主張しない。
使われ方：同じ実 cone の構造辺へ渡す元の実 fiber 比較。 -/
theorem dgKappaNativeBFFiberComparison_spaceEvaluation_isInvertible (n : ℕ)
    (h : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare ((dgKappaNativeBFSquare R D I hBF) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (spectrumSpaceEvaluation n))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (X := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{max (u + 1) v})
      ((dgKappaNativeBFFiberComparison R D I hBF).map
        ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (spectrumSpaceEvaluation n)))) := by
  let Q := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (spectrumSpaceEvaluation n)
  let p := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan (dgKappaNativeBFSquare R D I hBF)
  let e := (dgKappaNativeBFFiberConeComparison R D I hBF).map
    ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverPostcomp p Q))
  have hc := (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.isLimitCone_map_pullbackCone_iff Q (dgKappaNativeBFSquare R D I hBF)).mpr h
  have hd := dgKappaNativeBFKLimitCone_spaceEvaluation_isLimit R D I hBF n
  have he : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (X := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (p ≫ Q)) e :=
    isIso_of_isTerminal hc.isTerminalHo hd.isTerminalHo _
  have hp := he.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (p ≫ Q))
  have eqp := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.sliceOverPostcomp_projection p Q
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (X := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{max (u + 1) v})
    ((dgKappaNativeBFFiberConeComparison R D I hBF).map
      ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection p ≫ Q)))
  rw [← eqp]
  exact hp

/-- 概要：全正段での元の四角形の引き戻し性は、元の Sp 四角形へ反映される。
方針：同じ未完備 BF 四角形と元の錐比較へ既存の判定を適用する。
規約：有限 BF 供給命題に条件付き。固定 K の完備化後の引き戻し性は主張しない。
使われ方：同じ実 cone の構造辺へ渡す元の実 fiber 比較。 -/
theorem dgKappaNativeBFK_isPullback_of_positive_spaceEvaluation
    (h : ∀ r : ℕ, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare ((dgKappaNativeBFSquare R D I hBF) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (spectrumSpaceEvaluation (r + 1)))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare (dgKappaNativeBFSquare R D I hBF) := by
  apply (dgKappaNativeBFK_isPullback_iff_fiberComparison_isInvertible R D I hBF).mpr
  exact spectrumEdge_isInvertible_of_positive_spaceEvaluation
    (SSet.Edge.ofTruncated (dgKappaNativeBFFiberComparison R D I hBF))
    (fun r => dgKappaNativeBFFiberComparison_spaceEvaluation_isInvertible R D I hBF (r + 1) (h r))


end SerrePositivity.KST.NonConnective
