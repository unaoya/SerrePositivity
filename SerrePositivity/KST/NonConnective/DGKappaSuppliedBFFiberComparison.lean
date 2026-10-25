module
public import SerrePositivity.KST.NonConnective.DGKappaSuppliedBFZero
public import SerrePositivity.KST.Fibration.DGRelativeSpaceDetection

/-!
概要：同じ未完備 BF 四角形の元の実 fiber 比較を構成する。
方針：新 coherent 右辺・上辺の同じ cospan の実極限錐と全錐を比較し、全正段の検出を消費する。
規約：供給済みの実 BF 四角形を使用。一般 BF 整流や別の固定 K は導入しない。
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
open SerrePositivity.InfinityCategories.HomotopyLimits
open SerrePositivity.KST.SConstruction SerrePositivity.KST.Spectra
open SerrePositivity.KST.LocalizingInvariants SerrePositivity.KST.Fibration
namespace SerrePositivity.KST.NonConnective
local instance suppliedBFFiberSpectrumCategory : SimplicialCategory OmegaSpectrum.{w} :=
  OmegaSpectrum.simplicialCategory
variable (R : Type u) [CommRing R] (D : PerfDGInput.{u, max (u + 1) v} R)
  {κ : Cardinal.{u}} (I : DGKappaConeInput R D κ)

/-- 概要：元の K 四角形の右辺と上辺をそのまま底とする、Sp の構成済み極限錐。
方針：同じ未完備 BF 四角形と元の錐比較へ既存の判定を適用する。
規約：供給済みの実 BF 四角形を使用。旧 BF 右辺の fiber や固定 K の引き戻し性は主張しない。
使われ方：同じ実 cone の構造辺へ渡す元の実 fiber 比較。 -/
def dgKappaSuppliedBFKLimitCone : JoinCone (pullbackCospan (dgKappaNativeCoherentBFSquare R D I)) :=
  OmegaSpectrum.CoherentPullback.infinityCone _

/-- 概要：同じ実供給右辺・上辺の極限錐は実極限。
方針：Sp 正本の構成済み同じ極限性を使う。
規約：元の実供給 cospan を保持する。
使われ方：同じ実 fiber 四角形の認証。 -/
theorem dgKappaSuppliedBFKLimitCone_isLimit : IsLimitCone (dgKappaSuppliedBFKLimitCone R D I) :=
  OmegaSpectrum.CoherentPullback.infinityCone_isLimit _

/-- 概要：元の零角と右辺を変えず、左下の頂点を実 fiber に置き換えた四角形。
方針：同じ未完備 BF 四角形と元の錐比較へ既存の判定を適用する。
規約：供給済みの実 BF 四角形を使用。固定 K の完備化後の引き戻し性は主張しない。
使われ方：同じ実 cone の構造辺へ渡す元の実 fiber 比較。 -/
def dgKappaSuppliedBFCanonicalFiberSquare : FiberSquare
    (squareRightArrow (dgKappaNativeCoherentBFSquare R D I)) where
  square := coneSquare (dgKappaSuppliedBFKLimitCone R D I)
  zero_corner := by
    have ht : squareTopEdge ≫ coneSquare (dgKappaSuppliedBFKLimitCone R D I) =
        squareTopEdge ≫ (dgKappaNativeCoherentBFSquare R D I) := by
      rw [coneSquare_top]
      exact congrArg (fun q => q ≫ (dgKappaNativeCoherentBFSquare R D I))
        cospanSquareBoundary_topEdge
    have hz : squareVertex (coneSquare (dgKappaSuppliedBFKLimitCone R D I)) 0 1 =
        squareVertex (dgKappaNativeCoherentBFSquare R D I) 0 1 := by
      rw [← squareTopEdge_source, ht, squareTopEdge_source]
    rw [hz]
    exact dgKappaSuppliedBFSquare_zero_corner R D I
  right_edge := by
    rw [coneSquare_right]
    change horn₂₂.ι₀₂ ≫ pullbackCospan (dgKappaNativeCoherentBFSquare R D I) = _
    rw [pullbackCospan, ← Category.assoc, cospanSquareBoundary_rightEdge]
    rw [squareRightArrow_edge]
    exact (SSet.yonedaEquiv.symm_apply_apply
      (squareRightEdge ≫ (dgKappaNativeCoherentBFSquare R D I))).symm
  isPullback := coneSquare_isPullback _ (dgKappaSuppliedBFKLimitCone_isLimit R D I)

/-- 概要：比較元は元の K 四角形の全錐、比較先は同じ cospan の実極限錐。
方針：同じ未完備 BF 四角形と元の錐比較へ既存の判定を適用する。
規約：供給済みの実 BF 四角形を使用。固定 K の完備化後の引き戻し性は主張しない。
使われ方：同じ実 cone の構造辺へ渡す元の実 fiber 比較。 -/
def dgKappaSuppliedBFFiberConeComparison :
    SSet.Truncated.Edge (X := (truncation 2).obj
      (sliceOver (pullbackCospan (dgKappaNativeCoherentBFSquare R D I))))
      (pullbackCone (dgKappaNativeCoherentBFSquare R D I)) (dgKappaSuppliedBFKLimitCone R D I) :=
  Classical.choice ((dgKappaSuppliedBFKLimitCone_isLimit R D I).nonempty_edge _)

/-- 概要：全錐の同じ比較を頂点へ射影した、元の K 頂点から実 fiber への辺。
方針：同じ未完備 BF 四角形と元の錐比較へ既存の判定を適用する。
規約：供給済みの実 BF 四角形を使用。固定 K の完備化後の引き戻し性は主張しない。
使われ方：同じ実 cone の構造辺へ渡す元の実 fiber 比較。 -/
def dgKappaSuppliedBFFiberComparison :
    SSet.Truncated.Edge (X := (truncation 2).obj Sp.{max (u + 1) v})
      (pullbackCone (dgKappaNativeCoherentBFSquare R D I)).vertex
        (dgKappaSuppliedBFKLimitCone R D I).vertex :=
  (dgKappaSuppliedBFFiberConeComparison R D I).map ((truncation 2).map (sliceOverProjection _))

/-- 概要：同じ比較辺と、比較元・比較先の各元の脚の実合成三角形。
方針：同じ未完備 BF 四角形と元の錐比較へ既存の判定を適用する。
規約：供給済みの実 BF 四角形を使用。固定 K の完備化後の引き戻し性は主張しない。
使われ方：同じ実 cone の構造辺へ渡す元の実 fiber 比較。 -/
def dgKappaSuppliedBFFiberComparisonLegTriangle
    (k : (horn 2 2 : SSet.{max (u + 1) v + 1}) _⦋0⦌) :
    SSet.Truncated.Edge.CompStruct (dgKappaSuppliedBFFiberComparison R D I)
      (F2.nativeConeLeg (dgKappaSuppliedBFKLimitCone R D I) k)
      (F2.nativeConeLeg (pullbackCone (dgKappaNativeCoherentBFSquare R D I)) k) :=
  nativeConeComparisonLegTriangle (dgKappaSuppliedBFFiberConeComparison R D I) k

/-- 概要：元の相対 K 四角形が引き戻しとなる必要十分条件は、同じ実比較辺の可逆性。
方針：同じ未完備 BF 四角形と元の錐比較へ既存の判定を適用する。
規約：供給済みの実 BF 四角形を使用。固定 K の完備化後の引き戻し性は主張しない。
使われ方：同じ実 cone の構造辺へ渡す元の実 fiber 比較。 -/
theorem dgKappaSuppliedBFK_isPullback_iff_fiberComparison_isInvertible :
    IsPullbackSquare (dgKappaNativeCoherentBFSquare R D I) ↔
      IsInvertibleEdge (X := Sp.{max (u + 1) v}) (dgKappaSuppliedBFFiberComparison R D I) := by
  constructor
  · intro h
    have : IsIso (Truncated.HomotopyCategory.homMk
        (dgKappaSuppliedBFFiberConeComparison R D I)) :=
      isIso_of_isTerminal h.isTerminalHo (dgKappaSuppliedBFKLimitCone_isLimit R D I).isTerminalHo _
    change IsIso ((hoFunctor.map (sliceOverProjection _)).toFunctor.map
      (Truncated.HomotopyCategory.homMk (dgKappaSuppliedBFFiberConeComparison R D I)))
    infer_instance
  · intro h
    have he : IsInvertibleEdge (X := sliceOver
        (pullbackCospan (dgKappaNativeCoherentBFSquare R D I)))
        (dgKappaSuppliedBFFiberConeComparison R D I) :=
      rightFibration_reflects_isInvertibleEdge (sliceOverProjection _)
        (SSet.Edge.ofTruncated (dgKappaSuppliedBFFiberConeComparison R D I)) h
    have : IsIso (Truncated.HomotopyCategory.homMk
        (dgKappaSuppliedBFFiberConeComparison R D I)) := he
    exact (dgKappaSuppliedBFKLimitCone_isLimit R D I).of_vertexIso
      (asIso (Truncated.HomotopyCategory.homMk (dgKappaSuppliedBFFiberConeComparison R D I))).symm


/-- 概要：同じ cospan の canonical fiber 錐は、各実段評価後にも極限錐となる。
方針：同じ未完備 BF 四角形と元の錐比較へ既存の判定を適用する。
規約：供給済みの実 BF 四角形を使用。固定 K の完備化後の引き戻し性は主張しない。
使われ方：同じ実 cone の構造辺へ渡す元の実 fiber 比較。 -/
theorem dgKappaSuppliedBFKLimitCone_spaceEvaluation_isLimit (n : ℕ) :
    IsLimitCone ((dgKappaSuppliedBFKLimitCone R D I).postcomp
      (coherentNerveMap (spectrumSpaceEvaluation n))) := by
  let s := dgKappaSuppliedBFCanonicalFiberSquare R D I
  let t : ZeroTriangle Sp.{max (u + 1) v} := ⟨s.square, s.zero_corner⟩
  have h := spectrumFiberSquare_spaceEvaluation_isPullback t s.isPullback n
  have hc := (F2.isLimitCone_map_pullbackCone_iff
    (coherentNerveMap (spectrumSpaceEvaluation n)) s.square).mpr h
  apply (F2.isLimitCone_iff_of_cone_val_eq _ _ ?_).mp hc
  change (cospanConeSquareIso.hom ≫
    (cospanConeSquareIso.inv ≫ (dgKappaSuppliedBFKLimitCone R D I).val)) ≫ _ = _
  simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  rfl

/-- 概要：二つの評価錐が極限なら、同じ全錐比較を射影した評価辺は可逆。
方針：同じ未完備 BF 四角形と元の錐比較へ既存の判定を適用する。
規約：供給済みの実 BF 四角形を使用。固定 K の完備化後の引き戻し性は主張しない。
使われ方：同じ実 cone の構造辺へ渡す元の実 fiber 比較。 -/
theorem dgKappaSuppliedBFFiberComparison_spaceEvaluation_isInvertible (n : ℕ)
    (h : IsPullbackSquare ((dgKappaNativeCoherentBFSquare R D I) ≫
      coherentNerveMap (spectrumSpaceEvaluation n))) :
    IsInvertibleEdge (X := SpaceInfinity.{max (u + 1) v})
      ((dgKappaSuppliedBFFiberComparison R D I).map
        ((truncation 2).map (coherentNerveMap (spectrumSpaceEvaluation n)))) := by
  let Q := coherentNerveMap (spectrumSpaceEvaluation n)
  let p := pullbackCospan (dgKappaNativeCoherentBFSquare R D I)
  let e := (dgKappaSuppliedBFFiberConeComparison R D I).map
    ((truncation 2).map (sliceOverPostcomp p Q))
  have hc := (F2.isLimitCone_map_pullbackCone_iff Q (dgKappaNativeCoherentBFSquare R D I)).mpr h
  have hd := dgKappaSuppliedBFKLimitCone_spaceEvaluation_isLimit R D I n
  have he : IsInvertibleEdge (X := sliceOver (p ≫ Q)) e :=
    isIso_of_isTerminal hc.isTerminalHo hd.isTerminalHo _
  have hp := he.map (sliceOverProjection (p ≫ Q))
  have eqp := sliceOverPostcomp_projection p Q
  change IsInvertibleEdge (X := SpaceInfinity.{max (u + 1) v})
    ((dgKappaSuppliedBFFiberConeComparison R D I).map
      ((truncation 2).map (sliceOverProjection p ≫ Q)))
  rw [← eqp]
  exact hp

/-- 概要：全正段での元の四角形の引き戻し性は、元の Sp 四角形へ反映される。
方針：同じ未完備 BF 四角形と元の錐比較へ既存の判定を適用する。
規約：供給済みの実 BF 四角形を使用。固定 K の完備化後の引き戻し性は主張しない。
使われ方：同じ実 cone の構造辺へ渡す元の実 fiber 比較。 -/
theorem dgKappaSuppliedBFK_isPullback_of_positive_spaceEvaluation
    (h : ∀ r : ℕ, IsPullbackSquare ((dgKappaNativeCoherentBFSquare R D I) ≫
      coherentNerveMap (spectrumSpaceEvaluation (r + 1)))) :
    IsPullbackSquare (dgKappaNativeCoherentBFSquare R D I) := by
  apply (dgKappaSuppliedBFK_isPullback_iff_fiberComparison_isInvertible R D I).mpr
  exact spectrumEdge_isInvertible_of_positive_spaceEvaluation
    (SSet.Edge.ofTruncated (dgKappaSuppliedBFFiberComparison R D I))
    (fun r => dgKappaSuppliedBFFiberComparison_spaceEvaluation_isInvertible R D I (r + 1) (h r))


end SerrePositivity.KST.NonConnective
