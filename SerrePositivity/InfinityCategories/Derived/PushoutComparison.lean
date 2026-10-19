module
public import SerrePositivity.InfinityCategories.Derived.StableColimits
public import SerrePositivity.InfinityCategories.Derived.RebaseCocone
public import SerrePositivity.InfinityCategories.Derived.PullbackCriterion
public import SerrePositivity.InfinityCategories.Stable.InitialEdgeIso
public import SerrePositivity.InfinityCategories.Stable.InitialTransport

/-! # 標準 cofiber からの比較による押し出し判定

概要：任意の四角形が押し出しであることと、その標準 cofiber からの比較射の擬同型性を同定する。
方針：共通の span 上の余錐を比較し、始対象の一意性と左ファイブレーションの可逆性反映を使う。
規約：安定性は仮定しない。使われ方：D7 の fiber/cofiber 列の照合。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory DifferentialGraded DGNerve
open DGNerve.HomotopyComparison
open scoped Simplicial
variable {S : Type u} [CommRing S]
variable (F : (Δ[1] ⊗ Δ[1] : SSet.{u + 1}) ⟶ derivedInfinityCategory S)

/-- 元の四角形と同じ span を持つ標準 cofiber 正方形。 -/
abbrev derivedSquareCofiberSquare := derivedSpanCofiberSquare (pushoutSpan F)

/-- 標準 cofiber 正方形の span は元のものと等しい。 -/
lemma derivedSquareCofiberSquare_span :
    pushoutSpan (derivedSquareCofiberSquare F) = pushoutSpan F :=
  derivedSpanCofiberSquare_span (pushoutSpan F)

/-- 元の余錐を標準 cofiber の span 上へ読み替える。 -/
def derivedSquareCofiberComparisonCocone :
    JoinCocone (pushoutSpan (derivedSquareCofiberSquare F)) :=
  rebaseCocone (derivedSquareCofiberSquare_span F) (pushoutCocone F)

/-- 標準余錐から元の余錐への coslice の比較辺。 -/
def derivedSquareCofiberComparisonSliceEdge :
    SSet.Truncated.Edge (X := (SSet.truncation 2).obj
      (sliceUnder (pushoutSpan (derivedSquareCofiberSquare F))))
      (pushoutCocone (derivedSquareCofiberSquare F)) (derivedSquareCofiberComparisonCocone F) :=
  Classical.choice ((derivedSpanCofiberSquare_isPushout (pushoutSpan F)).nonempty_edge _)

/-- 比較辺を射影して得られる頂点間の辺。 -/
def derivedSquareCofiberComparisonEdge :
    SSet.Truncated.Edge (X := (SSet.truncation 2).obj (derivedInfinityCategory S))
      (pushoutCocone (derivedSquareCofiberSquare F)).vertex (pushoutCocone F).vertex :=
  (derivedSquareCofiberComparisonSliceEdge F).map ((SSet.truncation 2).map
    (sliceUnderProjection (pushoutSpan (derivedSquareCofiberSquare F))))

/-- 標準 cofiber から元の四角形の余錐頂点への実際の鎖写像。 -/
def derivedSquareCofiberComparison :=
  edgeChainMap ((derivedSquareCofiberComparisonEdge F).map
    ((SSet.truncation 2).map derivedInfinityInclusion))

/-- 押し出しの標準 cofiber 比較は擬同型。 -/
lemma derivedSquareCofiberComparison_quasiIso (hF : IsPushoutSquare F) :
    QuasiIso (derivedSquareCofiberComparison F) := by
  have hc := rebaseCocone_isColimit (derivedSquareCofiberSquare_span F) (pushoutCocone F) hF
  have := isIso_homMk_of_initial (derivedSpanCofiberSquare_isPushout (pushoutSpan F)) hc
    (derivedSquareCofiberComparisonSliceEdge F)
  have h₁ : IsIso (SSet.Truncated.HomotopyCategory₂.homMk
      (derivedSquareCofiberComparisonEdge F)) := by
    change IsIso ((HomotopyCategoryMap.map
      (sliceUnderProjection (pushoutSpan (derivedSquareCofiberSquare F)))).map
        (SSet.Truncated.HomotopyCategory₂.homMk (derivedSquareCofiberComparisonSliceEdge F)))
    infer_instance
  have h₂ : IsIso (SSet.Truncated.HomotopyCategory₂.homMk
      ((derivedSquareCofiberComparisonEdge F).map
        ((SSet.truncation 2).map derivedInfinityInclusion))) := by
    change IsIso ((HomotopyCategoryMap.map derivedInfinityInclusion).map
      (SSet.Truncated.HomotopyCategory₂.homMk (derivedSquareCofiberComparisonEdge F)))
    infer_instance
  obtain ⟨e, he⟩ := edgeChainMap_homotopyEquivalence
    ((derivedSquareCofiberComparisonEdge F).map
      ((SSet.truncation 2).map derivedInfinityInclusion)) h₂
  change QuasiIso (edgeChainMap _)
  rw [← he]
  infer_instance

/-- 比較射が擬同型なら元の四角形は ∞ 押し出し。 -/
lemma derived_isPushoutSquare_of_quasiIso (hF : QuasiIso (derivedSquareCofiberComparison F)) :
    IsPushoutSquare F := by
  have he := derived_edge_invertible_of_quasiIso (derivedSquareCofiberComparisonEdge F) hF
  have := leftFibration_reflects_invertibleEdge
    (sliceUnderProjection (pushoutSpan (derivedSquareCofiberSquare F)))
    (derivedSquareCofiberComparisonSliceEdge F) he
  have hc : IsColimitCone (derivedSquareCofiberComparisonCocone F) :=
    (derivedSpanCofiberSquare_isPushout (pushoutSpan F)).of_vertexIso
      (asIso (SSet.Truncated.HomotopyCategory.homMk (derivedSquareCofiberComparisonSliceEdge F)))
  exact (rebaseCocone_isColimit_iff (derivedSquareCofiberSquare_span F) (pushoutCocone F)).mp hc

/-- 任意の D(S) の四角形は標準 cofiber 比較の擬同型性で判定できる。 -/
theorem derived_isPushoutSquare_iff_quasiIso :
    IsPushoutSquare F ↔ QuasiIso (derivedSquareCofiberComparison F) :=
  ⟨derivedSquareCofiberComparison_quasiIso F, derived_isPushoutSquare_of_quasiIso F⟩

end SerrePositivity.InfinityCategories
