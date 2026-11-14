module
public import SerrePositivity.KST.NonConnective.DGKappaNativeBFArrowComparison

/-!
概要：同じ Φ の実右辺を、新 coherent BF 商射と旧射の π 作用へ照合する。
方針：同じ実四角形の端点だけを元の BF 対象へ戻し、新 BF 射を読み戻す。
規約：旧 kSpectrumMap との辺の等式や Sp fiber の同定は主張しない。
使われ方：実 fiber に使う右辺と K-S•-S3・旧 K-cof の群作用の接続。
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
namespace SerrePositivity.KST.NonConnective
local instance nativeBFRightSpectrumCategory : SimplicialCategory OmegaSpectrum.{w} :=
  OmegaSpectrum.simplicialCategory
variable (R : Type u) [CommRing R] (D : PerfDGInput.{u, max (u + 1) v} R)
  {κ : Cardinal.{u}} (I : DGKappaConeInput R D κ)
  (hBF : dgKappaNativeBFSquareComparison R D I)

/-- 概要：同じ実 Φ の右辺を元の未完備 cone・実商の BF 頂点で読む。
方針：同じ右辺の端点だけを指定頂点へ戻す。
規約：辺そのものを旧 BF 射へ取り替えない。
使われ方：同じ実 fiber 右辺の実 BF 射への読戻し。 -/
def dgKappaNativeBFSquareRightEdge : Sp.{max (u + 1) v}.Edge
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (kOmegaSpectrum (dgKappaNativeResolvedCone R D I)))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (kOmegaSpectrum
      (stableCategoryModel (dgKappaNativeSuspensionCategory R D I)))) :=
  (SSet.Edge.ofTruncated (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareRightArrow (dgKappaNativeBFSquare R D I hBF))).ofEq
    (dgKappaNativeBFSquare_middle R D I hBF) (dgKappaNativeBFSquare_target R D I hBF)

/-- 概要：同じ Φ から読む実右辺は新 coherent BF 射の辺そのもの。
方針：同じ実四角形の右境界を全一単体として回収する。
規約：旧 kSpectrumMap との等式ではない。
使われ方：実 fiber の右辺に指定正段比較と整数 π 一致を適用する。 -/
theorem dgKappaNativeBFSquareRightEdge_eq :
    dgKappaNativeBFSquareRightEdge R D I hBF =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (dgKappaNativeBFBoundary R D I hBF).right := by
  apply SSet.Edge.ext
  change (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareRightArrow (dgKappaNativeBFSquare R D I hBF)).edge = _
  have he := congrArg (fun F : (Δ[1] : SSet.{max (u + 1) v + 1}) ⟶
      Sp.{max (u + 1) v} => SSet.yonedaEquiv F)
    (dgKappaNativeBFSquare_right R D I hBF)
  exact (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareRightArrow_edge _).trans (he.trans
    (SSet.yonedaEquiv.apply_symm_apply
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (dgKappaNativeBFBoundary R D I hBF).right).edge))

/-- 概要：同じ実 Φ から読み戻す未完備 cone から実商への BF 射。
方針：同じ元の BF 端点を持つ実右辺を復号する。
規約：旧 BF 商射への同一視はしない。
使われ方：実 fiber 右辺の整数 π の比較。 -/
def dgKappaNativeBFSquareRightMap : kOmegaSpectrum (dgKappaNativeResolvedCone R D I) ⟶
    kOmegaSpectrum (stableCategoryModel (dgKappaNativeSuspensionCategory R D I)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdgeToHom (dgKappaNativeBFSquareRightEdge R D I hBF)

/-- 概要：同じ実右辺の読戻しは指定された新 coherent BF 射そのもの。
方針：元の coherent 辺の順逆の回収式を使う。
規約：旧 BF 射と比較するのは後の π 作用だけ。
使われ方：同じ実 fiber の右辺に供給された比較を代入する。 -/
theorem dgKappaNativeBFSquareRightMap_eq :
    dgKappaNativeBFSquareRightMap R D I hBF = (dgKappaNativeBFBoundary R D I hBF).right := by
  rw [dgKappaNativeBFSquareRightMap, dgKappaNativeBFSquareRightEdge_eq,
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdgeToHom_edge]

/-- 概要：同じ実 fiber に使う右辺の全整数 π 作用は旧 BF 商射と一致する。
方針：実右辺を新 BF 射へ回収し、指定された同じ群作用の等式を使う。
規約：Sp の辺の類や fiber の同型はここから推論しない。
使われ方：旧 kSpectrumMap の群作用で述べた既存界面との接続。 -/
theorem dgKappaNativeBFSquareRightMap_homotopyMap_eq (j : ℤ) :
    OmegaSpectrum.homotopyMap (dgKappaNativeBFSquareRightMap R D I hBF) j =
      OmegaSpectrum.homotopyMap (kSpectrumMap
        (sInputExactMap (dgKappaNativeVerdierDiagram R D I).projection)) j := by
  rw [dgKappaNativeBFSquareRightMap_eq]
  exact (dgKappaNativeBFBoundary R D I hBF).right_pi j

end SerrePositivity.KST.NonConnective
