module
public import SerrePositivity.KST.Fibration.Relative.CanonicalSuspensionInput

/-!
概要：K-6 の c5 のみを入力とする連結 fibration 結論と K-7 向け出力を一葉で公開する。
方針：同じ native 実列の d と、実共終性を代入済みの e を一つの結論へ束ねる。
規約：K(C)→K(C/D) は同じ実供給 BF 右辺。旧固定右辺への輸送は含めない。
使われ方：Sp の依頼どおりの c5 を一回代入して、同じ実比較と実構造射を得る。

BF 中央対象は `dgKappaNativeBFFiniteOmegaSpectrum R D I
  (dgKappaNativeBFFiniteNativeObject R D I 1)`、商対象は同じ式の添字 3。
商射は `(dgKappaNativeCoherentBFArrow R D I 1).hom`。
結論の `quotient_edge` が、この商射と指定 Sp fiber の実右辺を照合する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories

open SerrePositivity.KST.SConstruction SerrePositivity.KST.Spectra
open SerrePositivity.KST.LocalizingInvariants SerrePositivity.KST.NonConnective
open SerrePositivity.SimplicialModel
namespace SerrePositivity.KST.Fibration.Relative
local instance connectiveFibrationSpectrumCategory : SimplicialCategory OmegaSpectrum.{w} :=
  OmegaSpectrum.simplicialCategory

variable (R : Type u) [CommRing R] (D : PerfDGInput.{u, max (u + 1) v} R)
  {κ : Cardinal.{u}} (I : DGKappaConeInput R D κ)

/-- 概要：d の同じ比較先は、元の実供給右辺の Sp fiber そのもの。
方針：構成済み実極限錐の頂点を同じ fiber 四角形の頂点へ照合する。
規約：右辺・零角・実極限錐を取り替えない。
使われ方：主定理の非負次数比較が指す fiber を型として固定する。 -/
theorem k6Fibration_fiberTarget :
    (dgKappaSuppliedBFKLimitCone R D I).vertex =
      (dgKappaSuppliedBFCanonicalFiberSquare R D I).fiber := by
  have h := congrArg (fun f => f.app (Opposite.op ⦋0⦌) (dgKappaSuppliedBFKLimitCone R D I))
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.sliceSquareDiagramMap_sourceEvaluation
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan (dgKappaNativeCoherentBFSquare R D I)))
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := Sp.{max (u + 1) v})
      (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex (𝟙 ((Δ[1] : SSet.{max (u + 1) v + 1}) ⊗ Δ[1])) 0 0)).app
      (Opposite.op ⦋0⦌) ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.sliceSquareDiagramMap _).app (Opposite.op ⦋0⦌)
        (dgKappaSuppliedBFKLimitCone R D I)) = _ at h
  rw [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.sliceSquareDiagramMap_vertex] at h
  exact h.symm

/-- 概要：主定理の Sp fiber の右辺は指定した同じ BF 商射である。
方針：実 fiber の右辺回収と、元の全 BF 四角形の境界回収を合成する。
規約：頂点同型や群作用から射の比較を推論しない。
使われ方：K-B3 が L10 の同じ実 BF 右辺と照合する。 -/
theorem k6Fibration_quotientEdge :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫ (dgKappaSuppliedBFCanonicalFiberSquare R D I).square =
      SSet.yonedaEquiv.symm
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (dgKappaNativeCoherentBFArrow R D I 1).hom).edge := by
  calc
    _ = _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫ dgKappaNativeCoherentBFSquare R D I := by
      rw [(dgKappaSuppliedBFCanonicalFiberSquare R D I).right_edge, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareRightArrow_edge]
      exact SSet.yonedaEquiv.symm_apply_apply _
    _ = _ := dgKappaNativeCoherentBFSquare_boundary R D I 1

/-- 概要：元の固定 K(D) の実 fiber 比較と、BGT 入力となる同じ実構造射の結論。
方針：d の非負次数 π 同型、完備化比較、e の元の隣接射を記録する。
規約：新しい存在仮定を加えず、全入力自然性・非連結局所化性は含めない。
使われ方：K-B3 が一回の c5 代入結果から各結論を射影する。 -/
structure K6FibrationConclusions : Prop where
  fiber_target : (dgKappaSuppliedBFKLimitCone R D I).vertex =
    (dgKappaSuppliedBFCanonicalFiberSquare R D I).fiber
  quotient_edge : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫ (dgKappaSuppliedBFCanonicalFiberSquare R D I).square =
    SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (dgKappaNativeCoherentBFArrow R D I 1).hom).edge
  fiber_nonnegative : ∀ j : ℤ, 0 ≤ j →
    Function.Bijective (SpectrumHo.piMap (Truncated.HomotopyCategory.homMk
      (dgKappaCanonicalFixedSourceFiberComparison R D I).toTruncated) j)
  completion_positive : ∀ j : ℤ, 0 < j →
    Function.Bijective (OmegaSpectrum.homotopyMap (dgKappaRawSuspensionToFixedK R D I) j)
  completion_zero_injective :
    Function.Injective (OmegaSpectrum.homotopyMap (dgKappaRawSuspensionToFixedK R D I) 0)
  completionLoop_nonnegative : ∀ j : ℤ, 0 ≤ j →
    Function.Bijective (SpectrumHo.piMap (Truncated.HomotopyCategory.homMk
      (dgKappaRawSuspensionToFixedLoopEdge R D I).toTruncated) j)
  suspension_nonnegative : ∀ (Z : DGKappaZeroInput R D I) (j : ℤ), 0 ≤ j →
    Function.Bijective (OmegaSpectrum.homotopyMap
      (dgKappaCanonicalSuspensionStructureMap R D I Z) j)

-- h は元の同じ実列。依頼した c5 の型を別の供給命題へ包み直さない。

/-- 概要：依頼どおりの c5 一つから連結 fibration 結論と e の整理出力を得る。
方針：既存の同じ実 fiber 比較・完備化比較・固定 K 構造射判定へ一回ずつ渡す。
規約：hc5 の Prop は Sp へ送った依頼文のまま。I 以外の実図式供給は要求しない。
使われ方：Sp の同じ型の証明を一回代入する K-6 の条件付き公開主定理。 -/
theorem k6FibrationOfC5 :
    let h := dgKappaNativeVerdierDiagram R D I
    (hc5 : ∀ n : ℕ, IsIso (AnodyneHomotopy.anodyneQ.map (relativeFirstRowSimplexQuotient h.projection n))) →
      K6FibrationConclusions R D I := by
  dsimp only
  intro hc5
  exact {
    fiber_target := k6Fibration_fiberTarget R D I
    quotient_edge := k6Fibration_quotientEdge R D I
    fiber_nonnegative := dgKappaCanonicalFixedSourceFiberComparison_nonnegative R D I hc5
    completion_positive := dgKappaCanonicalCompletion_positive R D I
    completion_zero_injective := dgKappaCanonicalCompletion_zero_injective R D I
    completionLoop_nonnegative := dgKappaCanonicalCompletionLoop_nonnegative R D I
    suspension_nonnegative := fun Z =>
      dgKappaCanonicalSuspensionStructureMap_nonnegative R D I Z hc5 }

end SerrePositivity.KST.Fibration.Relative
