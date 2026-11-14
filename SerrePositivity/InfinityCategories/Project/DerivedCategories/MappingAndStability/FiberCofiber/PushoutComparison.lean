module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Triangles.StableColimits
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Homotopies.HomotopyModels.RebaseCocone
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.FiberCofiber.PullbackCriterion
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.InitialEdgeIso
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.InitialTransport

/-! # 標準 cofiber からの比較による押し出し判定

概要：任意の四角形が押し出しであることと、その標準 cofiber からの比較射の擬同型性を同定する。
方針：共通の span 上の余錐を比較し、始対象の一意性と左ファイブレーションの可逆性反映を使う。
規約：安定性は仮定しない。使われ方：D7 の fiber/cofiber 列の照合。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory MonoidalCategory DifferentialGraded

open scoped _root_.Simplicial
variable {S : Type u} [CommRing S]
variable (F : (Δ[1] ⊗ Δ[1] : SSet.{u + 1}) ⟶ _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory S)

/-- 元の四角形と同じ span を持つ標準 cofiber 正方形。 -/
abbrev derivedSquareCofiberSquare := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSpanCofiberSquare (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan F)

/-- 標準 cofiber 正方形の span は元のものと等しい。 -/
lemma derivedSquareCofiberSquare_span :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan (derivedSquareCofiberSquare F) = _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan F :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSpanCofiberSquare_span (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan F)

/-- 元の余錐を標準 cofiber の span 上へ読み替える。 -/
def derivedSquareCofiberComparisonCocone :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan (derivedSquareCofiberSquare F)) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.rebaseCocone (derivedSquareCofiberSquare_span F) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutCocone F)

/-- 標準余錐から元の余錐への coslice の比較辺。 -/
def derivedSquareCofiberComparisonSliceEdge :
    SSet.Truncated.Edge (X := (SSet.truncation 2).obj
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan (derivedSquareCofiberSquare F))))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutCocone (derivedSquareCofiberSquare F)) (derivedSquareCofiberComparisonCocone F) :=
  Classical.choice ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSpanCofiberSquare_isPushout (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan F)).nonempty_edge _)

/-- 比較辺を射影して得られる頂点間の辺。 -/
def derivedSquareCofiberComparisonEdge :
    SSet.Truncated.Edge (X := (SSet.truncation 2).obj (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory S))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutCocone (derivedSquareCofiberSquare F)).vertex (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutCocone F).vertex :=
  (derivedSquareCofiberComparisonSliceEdge F).map ((SSet.truncation 2).map
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan (derivedSquareCofiberSquare F))))

/-- 標準 cofiber から元の四角形の余錐頂点への実際の鎖写像。 -/
def derivedSquareCofiberComparison :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.edgeChainMap ((derivedSquareCofiberComparisonEdge F).map
    ((SSet.truncation 2).map _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityInclusion))

/-- 押し出しの標準 cofiber 比較は擬同型。 -/
lemma derivedSquareCofiberComparison_quasiIso (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare F) :
    QuasiIso (derivedSquareCofiberComparison F) := by
  have hc := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.rebaseCocone_isColimit (derivedSquareCofiberSquare_span F) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutCocone F) hF
  have := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.isIso_homMk_of_initial (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSpanCofiberSquare_isPushout (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan F)) hc
    (derivedSquareCofiberComparisonSliceEdge F)
  have h₁ : IsIso (SSet.Truncated.HomotopyCategory₂.homMk
      (derivedSquareCofiberComparisonEdge F)) := by
    change IsIso ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.map
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan (derivedSquareCofiberSquare F)))).map
        (SSet.Truncated.HomotopyCategory₂.homMk (derivedSquareCofiberComparisonSliceEdge F)))
    infer_instance
  have h₂ : IsIso (SSet.Truncated.HomotopyCategory₂.homMk
      ((derivedSquareCofiberComparisonEdge F).map
        ((SSet.truncation 2).map _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityInclusion))) := by
    change IsIso ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.map _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityInclusion).map
      (SSet.Truncated.HomotopyCategory₂.homMk (derivedSquareCofiberComparisonEdge F)))
    infer_instance
  obtain ⟨e, he⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.edgeChainMap_homotopyEquivalence
    ((derivedSquareCofiberComparisonEdge F).map
      ((SSet.truncation 2).map _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityInclusion)) h₂
  change QuasiIso (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.edgeChainMap _)
  rw [← he]
  infer_instance

/-- 比較射が擬同型なら元の四角形は ∞ 押し出し。 -/
lemma derived_isPushoutSquare_of_quasiIso (hF : QuasiIso (derivedSquareCofiberComparison F)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare F := by
  have he := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derived_edge_invertible_of_quasiIso (derivedSquareCofiberComparisonEdge F) hF
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.leftFibration_reflects_invertibleEdge
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan (derivedSquareCofiberSquare F)))
    (derivedSquareCofiberComparisonSliceEdge F) he
  have hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (derivedSquareCofiberComparisonCocone F) :=
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSpanCofiberSquare_isPushout (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan F)).of_vertexIso
      (asIso (SSet.Truncated.HomotopyCategory.homMk (derivedSquareCofiberComparisonSliceEdge F)))
  exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.rebaseCocone_isColimit_iff (derivedSquareCofiberSquare_span F) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutCocone F)).mp hc

/-- 任意の D(S) の四角形は標準 cofiber 比較の擬同型性で判定できる。 -/
theorem derived_isPushoutSquare_iff_quasiIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare F ↔ QuasiIso (derivedSquareCofiberComparison F) :=
  ⟨derivedSquareCofiberComparison_quasiIso F, derived_isPushoutSquare_of_quasiIso F⟩

end SerrePositivity.InfinityCategories.Project.DerivedCategories
