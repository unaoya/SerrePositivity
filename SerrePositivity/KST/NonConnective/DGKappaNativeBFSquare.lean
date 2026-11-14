module
public import SerrePositivity.KST.NonConnective.DGKappaNativeBFBoundaryInput
/-!
概要：同じ D-9 の未完備実列だけの有限 BF 四角形比較を消費する。
方針：採用済み供給命題を明示引数に取り、新四辺と各正段の全図式比較、旧 BF 射との整数 π 一致を回収する。
規約：供給命題の存在を主張せず、固定 S・ν・K と同じ I を保持する。
使われ方：K-6 の未完備全 S• 四角形から BF 四角形への受け渡し。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction SerrePositivity.KST.Spectra
open SerrePositivity.KST.LocalizingInvariants SerrePositivity.KST.Fibration
open SerrePositivity.KST.NonConnective
namespace SerrePositivity.KST.NonConnective
local instance rawBFComparisonSpectrumCategory : SimplicialCategory OmegaSpectrum.{w} :=
  OmegaSpectrum.simplicialCategory
variable (R : Type u) [CommRing R] (D : PerfDGInput.{u, max (u + 1) v} R)
  {κ : Cardinal.{u}} (I : DGKappaConeInput R D κ)
/-- 概要：同じ未完備実列に限る新 coherent BF 四角形の供給命題。
方針：新四辺の正段指定比較・旧 BF 射との整数 π 一致を含む同じデータを要求する。
規約：K-S•-S3 の型変更に従い、旧 kSpectrumMap の辺との厳密等式は要求しない。
使われ方：実供給までの明示定理引数。存在は主張しない。 -/
def dgKappaNativeBFSquareComparison : Prop := Nonempty (DGKappaNativeBFBoundaryInput R D I)

variable (hBF : dgKappaNativeBFSquareComparison R D I)

/-- 概要：同じ新 coherent BF 四角形の指定境界・正段比較・整数 π 一致を保持する。
方針：同じ採用済み供給命題のデータを取り出す。
規約：旧 BF 辺との等式を追加しない。
使われ方：同じ実 fiber と旧共終性界面の比較。 -/
def dgKappaNativeBFBoundary : DGKappaNativeBFBoundaryInput R D I := Classical.choice hBF

/-- 概要：同じ供給に条件付きの未完備実列の実 coherent BF 四角形。
方針：指定比較と整数 π の一致を伴う同じ四角形を取り出す。
規約：同じ実核・cone・実商の BF 頂点を保持する。
使われ方：同じ実 fiber 比較の入力四角形。 -/
def dgKappaNativeBFSquare :
    (Δ[1] ⊗ Δ[1] : SSet.{max (u + 1) v + 1}) ⟶ Sp.{max (u + 1) v} :=
  (dgKappaNativeBFBoundary R D I hBF).square

/-- 概要：同じ BF 四角形の bottom 辺は新しい coherent BF 射そのもの。
方針：供給データの同じ指定境界を回収する。
規約：旧 kSpectrumMap との厳密等式ではない。
使われ方：元の四 BF 頂点と同じ実境界の回収。 -/
theorem dgKappaNativeBFSquare_bottom :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ dgKappaNativeBFSquare R D I hBF = SSet.yonedaEquiv.symm
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (dgKappaNativeBFBoundary R D I hBF).bottom).edge :=
  (dgKappaNativeBFBoundary R D I hBF).bottom_edge

/-- 概要：同じ BF 四角形の right 辺は新しい coherent BF 射そのもの。
方針：供給データの同じ指定境界を回収する。
規約：旧 kSpectrumMap との厳密等式ではない。
使われ方：元の四 BF 頂点と同じ実境界の回収。 -/
theorem dgKappaNativeBFSquare_right :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫ dgKappaNativeBFSquare R D I hBF = SSet.yonedaEquiv.symm
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (dgKappaNativeBFBoundary R D I hBF).right).edge :=
  (dgKappaNativeBFBoundary R D I hBF).right_edge

/-- 概要：同じ BF 四角形の left 辺は新しい coherent BF 射そのもの。
方針：供給データの同じ指定境界を回収する。
規約：旧 kSpectrumMap との厳密等式ではない。
使われ方：元の四 BF 頂点と同じ実境界の回収。 -/
theorem dgKappaNativeBFSquare_left :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareLeftEdge ≫ dgKappaNativeBFSquare R D I hBF = SSet.yonedaEquiv.symm
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (dgKappaNativeBFBoundary R D I hBF).left).edge :=
  (dgKappaNativeBFBoundary R D I hBF).left_edge

/-- 概要：同じ BF 四角形の top 辺は新しい coherent BF 射そのもの。
方針：供給データの同じ指定境界を回収する。
規約：旧 kSpectrumMap との厳密等式ではない。
使われ方：元の四 BF 頂点と同じ実境界の回収。 -/
theorem dgKappaNativeBFSquare_top :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareTopEdge ≫ dgKappaNativeBFSquare R D I hBF = SSet.yonedaEquiv.symm
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (dgKappaNativeBFBoundary R D I hBF).top).edge :=
  (dgKappaNativeBFBoundary R D I hBF).top_edge

/-- 概要：同じ BF 四角形の各正段を、元の境界商の全四角形へ比較する。
方針：同じ供給命題の全図式同型を取り出す。
規約：四頂点・四辺や π 群だけの照合へ弱めない。
使われ方：K-6 の全 S• 比較を同じ BF 四角形へ渡す。 -/
def dgKappaNativeBFBoundarySquareIso (r : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
      (dgKappaNativeBFSquare R D I hBF ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (spectrumSpaceEvaluation.{max (u + 1) v} (r + 1)))
      ((dgKappaNativeVerdierDiagram R D I).square ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (stableBoundaryClosedKanEnrichedFunctor.{max (u + 1) v} r)) :=
  Classical.choice ((dgKappaNativeBFBoundary R D I hBF).positive r)

/-- 概要：元の全正反復 S• 四角形を同じ BF 正段の全四角形へ比較する。
方針：元の全境界商比較と供給された同じ実正段比較を合成する。
規約：指定二胞体を含む全図式同型である。供給命題に条件付き。
使われ方：未完備 fibration の全 S• 像から同じ BF 四角形への受け渡し。 -/
def dgKappaNativeBFMultiSquareIso (r : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
      ((dgKappaNativeVerdierDiagram R D I).square ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (stableMultiKanEnrichedFunctor.{max (u + 1) v} r))
      (dgKappaNativeBFSquare R D I hBF ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (spectrumSpaceEvaluation.{max (u + 1) v} (r + 1))) :=
  (stableBoundaryQuotientKanIso r).precomp (dgKappaNativeVerdierDiagram R D I).square ≪≫
    (dgKappaNativeBFBoundarySquareIso R D I hBF r).symm

/-- 概要：供給命題に条件付きで、同じ元の全 S• 四角形の引き戻しを BF 正段へ渡す。
方針：指定全図式の同型で同じ引き戻し性を輸送する。
規約：全 S• fibration の証明や供給命題の存在は主張しない。
使われ方：K-6 c5 の完備化前の fibration からの受け渡し。 -/
theorem dgKappaNativeBF_spaceEvaluation_isPullback (r : ℕ)
    (hS : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare ((dgKappaNativeVerdierDiagram R D I).square ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (stableMultiKanEnrichedFunctor.{max (u + 1) v} r))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare (dgKappaNativeBFSquare R D I hBF ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (spectrumSpaceEvaluation.{max (u + 1) v} (r + 1))) :=
  hS.of_functorIso (dgKappaNativeBFMultiSquareIso R D I hBF r)

/-- 概要：同じ BF 四角形の左下は元の未完備実核 K の頂点。
方針：同じ指定下辺の始点を回収する。
規約：元の実核の K 値を保持する。
使われ方：実 fiber 比較の始点の厳密照合。 -/
theorem dgKappaNativeBFSquare_source :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex (dgKappaNativeBFSquare R D I hBF) 0 0 =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (kOmegaSpectrum
        (stableCategoryModel (dgKappaNativeKernelCategory R D I))) := by
  have h := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareBottomEdge_source (dgKappaNativeBFSquare R D I hBF)
  rw [dgKappaNativeBFSquare_bottom] at h
  have hv := congrArg (fun t : Sp.{max (u + 1) v} _⦋1⦌ =>
    Sp.{max (u + 1) v}.δ 1 t)
    (SSet.yonedaEquiv.apply_symm_apply
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (dgKappaNativeBFBoundary R D I hBF).bottom).edge)
  exact h.symm.trans (hv.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge _).src_eq)

/-- 概要：同じ BF 四角形の右下は元の未完備実平坦 cone K の頂点。
方針：同じ指定下辺の終点を回収する。
規約：元の cell 分解源の K 値を保持する。
使われ方：同じ cone の K 零性の代入。 -/
theorem dgKappaNativeBFSquare_middle :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex (dgKappaNativeBFSquare R D I hBF) 1 0 =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (kOmegaSpectrum (dgKappaNativeResolvedCone R D I)) := by
  have h := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareBottomEdge_target (dgKappaNativeBFSquare R D I hBF)
  rw [dgKappaNativeBFSquare_bottom] at h
  have hv := congrArg (fun t : Sp.{max (u + 1) v} _⦋1⦌ =>
    Sp.{max (u + 1) v}.δ 0 t)
    (SSet.yonedaEquiv.apply_symm_apply
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (dgKappaNativeBFBoundary R D I hBF).bottom).edge)
  exact h.symm.trans (hv.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge _).tgt_eq)

/-- 概要：同じ BF 四角形の右上は元の未完備実商 K の頂点。
方針：同じ指定右辺の終点を回収する。
規約：Perf 完備化後の値へ置き換えない。
使われ方：同じ未完備実商の loop と固定 K の間の接続。 -/
theorem dgKappaNativeBFSquare_target :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex (dgKappaNativeBFSquare R D I hBF) 1 1 =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (kOmegaSpectrum
        (stableCategoryModel (dgKappaNativeSuspensionCategory R D I))) := by
  have h := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareRightEdge_target (dgKappaNativeBFSquare R D I hBF)
  rw [dgKappaNativeBFSquare_right] at h
  have hv := congrArg (fun t : Sp.{max (u + 1) v} _⦋1⦌ =>
    Sp.{max (u + 1) v}.δ 0 t)
    (SSet.yonedaEquiv.apply_symm_apply
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (dgKappaNativeBFBoundary R D I hBF).right).edge)
  exact h.symm.trans (hv.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge _).tgt_eq)

end SerrePositivity.KST.NonConnective
