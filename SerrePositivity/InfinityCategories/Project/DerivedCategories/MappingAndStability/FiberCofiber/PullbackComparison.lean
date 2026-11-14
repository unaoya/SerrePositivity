module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.FiberCofiber.PullbackPresentation

/-! # 導来 ∞ 圏の引き戻しと標準 fiber の比較

概要：D(S) の引き戻し四角形の頂点から標準 fiber への誘導射は擬同型である。
方針：同じ cospan 上の二つの極限錐を比較し、辺の同型性を複体のホモトピー同値へ移す。
規約：四角形の極限性以外の追加前提はない。使われ方：D4 の必要条件。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory MonoidalCategory DifferentialGraded

open scoped _root_.Simplicial
variable {S : Type u} [CommRing S]

/-- 概要：任意の四角形の錐を標準 fiber 四角形の cospan 上で読む。
方針：同じ cospan であることを用いて固定条件だけを読み替える。
規約：元の錐の頂点は変えない。使われ方：標準錐との比較辺の始点。 -/
def derivedSquareComparisonCone
    (F : (Δ[1] ⊗ Δ[1] : SSet.{u + 1}) ⟶ _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory S) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquareFiberSquare F)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.rebaseCone (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquareFiberSquare_cospan F) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCone F)

/-- 概要：任意の四角形から標準 fiber 錐への slice の比較辺。
方針：標準 fiber 錐の終対象性から辺を選ぶ。
規約：元の四角形の極限性は構成には不要。使われ方：誘導射の定義。 -/
def derivedSquareComparisonSliceEdge
    (F : (Δ[1] ⊗ Δ[1] : SSet.{u + 1}) ⟶ _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory S) :
    SSet.Truncated.Edge (X := (SSet.truncation 2).obj
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquareFiberSquare F))))
        (derivedSquareComparisonCone F) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCone (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquareFiberSquare F)) :=
  Classical.choice ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquareFiberSquare_isPullback F).nonempty_edge _)

/-- 概要：四角形の頂点から標準 fiber の頂点への比較辺。
方針：slice の比較辺を射影し、標準錐の頂点を fiber に同定する。
規約：元の四角形の極限性を仮定しない。使われ方：実際の鎖写像の抽出。 -/
def derivedSquareComparisonEdge
    (F : (Δ[1] ⊗ Δ[1] : SSet.{u + 1}) ⟶ _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory S) :
    SSet.Truncated.Edge (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.twoTruncation S (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree S))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCone F).vertex (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquareStandardFiber F)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.edgeTransportTarget (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquareFiberSquare_vertex F)
    ((derivedSquareComparisonSliceEdge F).map ((SSet.truncation 2).map
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquareFiberSquare F)))))

/-- 概要：引き戻し四角形の比較辺の類はホモトピー圏で同型である。
方針：slice の二つの終対象の間の辺の同型性を射影する。
規約：極限の一意性を用いる。使われ方：比較射のホモトピー同値性。 -/
lemma derivedSquareComparisonEdge_isIso
    (F : (Δ[1] ⊗ Δ[1] : SSet.{u + 1}) ⟶ _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory S)
    (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare F) :
    IsIso (SSet.Truncated.HomotopyCategory₂.homMk (derivedSquareComparisonEdge F)) := by
  have hc := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.rebaseCone_isLimit (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquareFiberSquare_cospan F) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCone F) hF
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.isIso_homMk_of_terminal hc (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquareFiberSquare_isPullback F)
    (derivedSquareComparisonSliceEdge F)
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.isIso_homMk_edgeTransportTarget
  change IsIso ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.map
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquareFiberSquare F)))).map
      (SSet.Truncated.HomotopyCategory₂.homMk (derivedSquareComparisonSliceEdge F)))
  infer_instance

/-- 概要：四角形の頂点から標準 fiber への実際の鎖写像。
方針：D(S) の比較辺を全複体へ包含し、閉零射を鎖写像として読む。
規約：標準 fiber は semifree。使われ方：D4 の擬同型となる比較射。 -/
def derivedSquareFiberComparison
    (F : (Δ[1] ⊗ Δ[1] : SSet.{u + 1}) ⟶ _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory S) :
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCone F).vertex.obj 0).val ⟶ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquareStandardFiber F).val :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.edgeChainMap ((derivedSquareComparisonEdge F).map ((SSet.truncation 2).map
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityInclusion))

/-- 概要：引き戻し四角形の頂点から標準 fiber への比較射はホモトピー同値である。
方針：比較辺の同型性を包含で保ち、N3 と複体ホモトピー圏の比較へ渡す。
規約：四角形の極限性以外の追加前提なし。使われ方：擬同型性より強い結論。 -/
lemma derivedSquareFiberComparison_homotopyEquivalence
    (F : (Δ[1] ⊗ Δ[1] : SSet.{u + 1}) ⟶ _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory S)
    (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare F) :
    HomologicalComplex.homotopyEquivalences (ModuleCat.{u} S) (.up ℤ)
      (derivedSquareFiberComparison F) := by
  have := derivedSquareComparisonEdge_isIso F hF
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.edgeChainMap_homotopyEquivalence
  change IsIso ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.map _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityInclusion).map
    (SSet.Truncated.HomotopyCategory₂.homMk (derivedSquareComparisonEdge F)))
  infer_instance

/-- 概要：D(S) の引き戻し四角形の頂点から標準 fiber への誘導射は擬同型である。
方針：同じ誘導射のホモトピー同値から全次数のホモロジー同型を得る。
規約：任意の可換環と非有界 semifree 複体。使われ方：BS 界面の引き戻しの必要条件。 -/
theorem derivedSquareFiberComparison_quasiIso
    (F : (Δ[1] ⊗ Δ[1] : SSet.{u + 1}) ⟶ _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory S)
    (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare F) : QuasiIso (derivedSquareFiberComparison F) := by
  obtain ⟨e, he⟩ := derivedSquareFiberComparison_homotopyEquivalence F hF
  rw [← he]
  infer_instance

end SerrePositivity.InfinityCategories.Project.DerivedCategories
