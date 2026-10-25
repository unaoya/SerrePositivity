module
public import SerrePositivity.KST.NonConnective.DGKappaNativeSquareComparison
public import SerrePositivity.KST.Fibration.SpectrumSpaceEvaluation
/-!
概要：同じ D-9 の未完備実列だけの有限 BF 四角形比較を消費する。
方針：採用済み供給命題を明示引数に取り、四辺と各正段の全図式比較を回収する。
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
/-- 概要：同じ未完備厳密 dg 実列に限る有限 BF 四角形の供給命題。
方針：元の四つの BF 射を固定し、全正段で同じ S• 全四角形への比較を要求する。
規約：採用済みの明示定理引数。命題の証明・存在や一般 K 関手化は主張しない。
使われ方：K-S• の実供給まで利用側の仮定引数として使う。 -/
def dgKappaNativeBFSquareComparison : Prop :=
  let d := dgKappaNativeVerdierDiagram R D I
  ∃ Φ : (Δ[1] ⊗ Δ[1] : SSet.{max (u + 1) v + 1}) ⟶ Sp.{max (u + 1) v},
    squareBottomEdge ≫ Φ = SSet.yonedaEquiv.symm
      (coherentNerveEdge (kSpectrumMap (sInputExactMap d.inclusion))).edge ∧
    squareRightEdge ≫ Φ = SSet.yonedaEquiv.symm
      (coherentNerveEdge (kSpectrumMap (sInputExactMap d.projection))).edge ∧
    squareLeftEdge ≫ Φ = SSet.yonedaEquiv.symm
      (coherentNerveEdge (kSpectrumMap (sInputExactMap (toZeroCategory d.left)))).edge ∧
    squareTopEdge ≫ Φ = SSet.yonedaEquiv.symm
      (coherentNerveEdge (kSpectrumMap (sInputExactMap (fromZeroCategory d.right)))).edge ∧
    ∀ r : ℕ, Nonempty (FunctorIso
      (Φ ≫ coherentNerveMap (spectrumSpaceEvaluation.{max (u + 1) v} (r + 1)))
      (d.square ≫ coherentNerveMap (stableBoundaryClosedKanEnrichedFunctor.{max (u + 1) v} r)))

variable (hBF : dgKappaNativeBFSquareComparison R D I)

/-- 概要：供給命題に条件付きの、同じ未完備実列の実 BF 四角形。
方針：元の四辺と全正段比較を含む同じ供給値を取り出す。
規約：別の実商・cone や固定 K を選び直さない。
使われ方：同じ実 fiber 比較の入力四角形。 -/
def dgKappaNativeBFSquare :
    (Δ[1] ⊗ Δ[1] : SSet.{max (u + 1) v + 1}) ⟶ Sp.{max (u + 1) v} :=
  Classical.choose hBF

/-- 概要：同じ BF 四角形の下辺は元の実核包含の K 射そのもの。
方針：供給命題の指定下辺を回収する。
規約：全一単体の厳密等式。
使われ方：元の実核包含の比較。 -/
theorem dgKappaNativeBFSquare_bottom :
    squareBottomEdge ≫ dgKappaNativeBFSquare R D I hBF = SSet.yonedaEquiv.symm
      (coherentNerveEdge (kSpectrumMap
        (sInputExactMap (dgKappaNativeVerdierDiagram R D I).inclusion))).edge :=
  (Classical.choose_spec hBF).1

/-- 概要：同じ BF 四角形の右辺は元の実商射の K 射そのもの。
方針：供給命題の指定右辺を回収する。
規約：全一単体の厳密等式。
使われ方：元の実右射の fiber の指定。 -/
theorem dgKappaNativeBFSquare_right :
    squareRightEdge ≫ dgKappaNativeBFSquare R D I hBF = SSet.yonedaEquiv.symm
      (coherentNerveEdge (kSpectrumMap
        (sInputExactMap (dgKappaNativeVerdierDiagram R D I).projection))).edge :=
  (Classical.choose_spec hBF).2.1

/-- 概要：同じ BF 四角形の左辺は元の零圏への完全射の K 射そのもの。
方針：供給命題の指定左辺を回収する。
規約：同じ元の零角と全一単体を保持する。
使われ方：実零角の照合。 -/
theorem dgKappaNativeBFSquare_left :
    squareLeftEdge ≫ dgKappaNativeBFSquare R D I hBF = SSet.yonedaEquiv.symm
      (coherentNerveEdge (kSpectrumMap
        (sInputExactMap (toZeroCategory (dgKappaNativeVerdierDiagram R D I).left)))).edge :=
  (Classical.choose_spec hBF).2.2.1

/-- 概要：同じ BF 四角形の上辺は元の零圏から実商への K 射そのもの。
方針：供給命題の指定上辺を回収する。
規約：元の零角・実商・全一単体を保持する。
使われ方：実 fiber 四角形の cospan の照合。 -/
theorem dgKappaNativeBFSquare_top :
    squareTopEdge ≫ dgKappaNativeBFSquare R D I hBF = SSet.yonedaEquiv.symm
      (coherentNerveEdge (kSpectrumMap
        (sInputExactMap (fromZeroCategory (dgKappaNativeVerdierDiagram R D I).right)))).edge :=
  (Classical.choose_spec hBF).2.2.2.1

/-- 概要：同じ BF 四角形の各正段を、元の境界商の全四角形へ比較する。
方針：同じ供給命題の全図式同型を取り出す。
規約：四頂点・四辺や π 群だけの照合へ弱めない。
使われ方：K-6 の全 S• 比較を同じ BF 四角形へ渡す。 -/
def dgKappaNativeBFBoundarySquareIso (r : ℕ) :
    FunctorIso
      (dgKappaNativeBFSquare R D I hBF ≫
        coherentNerveMap (spectrumSpaceEvaluation.{max (u + 1) v} (r + 1)))
      ((dgKappaNativeVerdierDiagram R D I).square ≫
        coherentNerveMap (stableBoundaryClosedKanEnrichedFunctor.{max (u + 1) v} r)) :=
  Classical.choice ((Classical.choose_spec hBF).2.2.2.2 r)

/-- 概要：元の全正反復 S• 四角形を同じ BF 正段の全四角形へ比較する。
方針：元の全境界商比較と供給された同じ実正段比較を合成する。
規約：指定二胞体を含む全図式同型である。供給命題に条件付き。
使われ方：未完備 fibration の全 S• 像から同じ BF 四角形への受け渡し。 -/
def dgKappaNativeBFMultiSquareIso (r : ℕ) :
    FunctorIso
      ((dgKappaNativeVerdierDiagram R D I).square ≫
        coherentNerveMap (stableMultiKanEnrichedFunctor.{max (u + 1) v} r))
      (dgKappaNativeBFSquare R D I hBF ≫
        coherentNerveMap (spectrumSpaceEvaluation.{max (u + 1) v} (r + 1))) :=
  (stableBoundaryQuotientKanIso r).precomp (dgKappaNativeVerdierDiagram R D I).square ≪≫
    (dgKappaNativeBFBoundarySquareIso R D I hBF r).symm

/-- 概要：供給命題に条件付きで、同じ元の全 S• 四角形の引き戻しを BF 正段へ渡す。
方針：指定全図式の同型で同じ引き戻し性を輸送する。
規約：全 S• fibration の証明や供給命題の存在は主張しない。
使われ方：K-6 c5 の完備化前の fibration からの受け渡し。 -/
theorem dgKappaNativeBF_spaceEvaluation_isPullback (r : ℕ)
    (hS : IsPullbackSquare ((dgKappaNativeVerdierDiagram R D I).square ≫
      coherentNerveMap (stableMultiKanEnrichedFunctor.{max (u + 1) v} r))) :
    IsPullbackSquare (dgKappaNativeBFSquare R D I hBF ≫
      coherentNerveMap (spectrumSpaceEvaluation.{max (u + 1) v} (r + 1))) :=
  hS.of_functorIso (dgKappaNativeBFMultiSquareIso R D I hBF r)

/-- 概要：同じ BF 四角形の左下は元の未完備実核 K の頂点。
方針：同じ指定下辺の始点を回収する。
規約：元の実核の K 値を保持する。
使われ方：実 fiber 比較の始点の厳密照合。 -/
theorem dgKappaNativeBFSquare_source :
    squareVertex (dgKappaNativeBFSquare R D I hBF) 0 0 =
      coherentNerveVertex (kOmegaSpectrum
        (stableCategoryModel (dgKappaNativeKernelCategory R D I))) := by
  have h := squareBottomEdge_source (dgKappaNativeBFSquare R D I hBF)
  rw [dgKappaNativeBFSquare_bottom] at h
  have hv := congrArg (fun t : Sp.{max (u + 1) v} _⦋1⦌ =>
    Sp.{max (u + 1) v}.δ 1 t)
    (SSet.yonedaEquiv.apply_symm_apply
      (coherentNerveEdge (kSpectrumMap
        (sInputExactMap (dgKappaNativeVerdierDiagram R D I).inclusion))).edge)
  exact h.symm.trans (hv.trans (coherentNerveEdge _).src_eq)

/-- 概要：同じ BF 四角形の右下は元の未完備実平坦 cone K の頂点。
方針：同じ指定下辺の終点を回収する。
規約：元の cell 分解源の K 値を保持する。
使われ方：同じ cone の K 零性の代入。 -/
theorem dgKappaNativeBFSquare_middle :
    squareVertex (dgKappaNativeBFSquare R D I hBF) 1 0 =
      coherentNerveVertex (kOmegaSpectrum (dgKappaNativeResolvedCone R D I)) := by
  have h := squareBottomEdge_target (dgKappaNativeBFSquare R D I hBF)
  rw [dgKappaNativeBFSquare_bottom] at h
  have hv := congrArg (fun t : Sp.{max (u + 1) v} _⦋1⦌ =>
    Sp.{max (u + 1) v}.δ 0 t)
    (SSet.yonedaEquiv.apply_symm_apply
      (coherentNerveEdge (kSpectrumMap
        (sInputExactMap (dgKappaNativeVerdierDiagram R D I).inclusion))).edge)
  exact h.symm.trans (hv.trans (coherentNerveEdge _).tgt_eq)

/-- 概要：同じ BF 四角形の右上は元の未完備実商 K の頂点。
方針：同じ指定右辺の終点を回収する。
規約：Perf 完備化後の値へ置き換えない。
使われ方：同じ未完備実商の loop と固定 K の間の接続。 -/
theorem dgKappaNativeBFSquare_target :
    squareVertex (dgKappaNativeBFSquare R D I hBF) 1 1 =
      coherentNerveVertex (kOmegaSpectrum
        (stableCategoryModel (dgKappaNativeSuspensionCategory R D I))) := by
  have h := squareRightEdge_target (dgKappaNativeBFSquare R D I hBF)
  rw [dgKappaNativeBFSquare_right] at h
  have hv := congrArg (fun t : Sp.{max (u + 1) v} _⦋1⦌ =>
    Sp.{max (u + 1) v}.δ 0 t)
    (SSet.yonedaEquiv.apply_symm_apply
      (coherentNerveEdge (kSpectrumMap
        (sInputExactMap (dgKappaNativeVerdierDiagram R D I).projection))).edge)
  exact h.symm.trans (hv.trans (coherentNerveEdge _).tgt_eq)

end SerrePositivity.KST.NonConnective
