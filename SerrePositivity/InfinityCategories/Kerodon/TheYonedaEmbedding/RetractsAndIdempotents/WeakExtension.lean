module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.WeakInnerAnodyne
public import SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.InnerAnodyneEquivalence
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：指定した元の弱い retract 図式は、強い分裂へ延長でき、その延長空間は可縮。
方針：元の比較への制限の trivial Kan fibration と、元の指定図式上の fiber を使う。
規約：元の弱い全図式を厳密に回収する。既に指定した全 Idem 図式の分裂とは区別する。
使われ方：HTT 4.4.5.6、ホモトピー圏の retract と coherent 分裂の比較。

対応節は Kerodon 8.5（Tag 03Y9）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents

/-- 元の弱い retract 添字への制限そのものは、任意の quasicategory に対して trivial Kan。 -/
@[kerodon 03Z7]
lemma weakComparisonRestriction_trivialKanFibration (X : SSet.{u}) [Quasicategory X] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration ((pre _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.weakComparison).app X) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.trivialKanFibration_pre_of_innerAnodyne _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.weakComparison _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.weakComparison_innerAnodyne X

/-- 元の弱い全 retract 図式を固定した、強い分裂への元の延長の空間。 -/
def weakDiagramExtensionSpace {X : SSet.{u}} (d : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.WeakRetractionDiagram X) : SSet.{u} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber ((pre _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.weakComparison).app X) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex d)

/-- 元の弱い全図式を固定した強い分裂への延長空間は可縮な Kan 複体。 -/
lemma weakDiagramExtensionSpace_isContractibleKan {X : SSet.{u}} [Quasicategory X]
    (d : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.WeakRetractionDiagram X) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan (weakDiagramExtensionSpace d) := by
  have := weakComparisonRestriction_trivialKanFibration X
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_isContractibleKan _ _

/-- 元の弱い全 retract 図式は、同じ制限で厳密に回収される強い全図式へ延長できる。 -/
lemma weakDiagram_extension_exists {X : SSet.{u}} [Quasicategory X]
    (d : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.WeakRetractionDiagram X) : ∃ s : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.SplitShape ⟶ X, _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.weakComparison ≫ s = d := by
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.weakComparison_innerAnodyne.{u} (terminal.from X)
    (InnerFibration.mem (q := terminal.from X))
  have sq : CommSq d _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.weakComparison (terminal.from X) (terminal.from _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.SplitShape) :=
    ⟨terminal.hom_ext _ _⟩
  exact ⟨sq.lift, sq.fac_left⟩

/-- 元の弱い retract は、元の全図式を保つ coherent な冪等図式の強い分裂を与える。 -/
lemma weakDiagram_strongSplitting_exists {X : SSet.{u}} [Quasicategory X]
    (d : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.WeakRetractionDiagram X) :
    ∃ (e : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.CoherentIdempotent X) (s : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.StrongSplitting e), s.weakDiagram = d := by
  obtain ⟨s, hs⟩ := weakDiagram_extension_exists d
  exact ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.idemInclusion ≫ s, ⟨s, rfl⟩, hs⟩

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents
