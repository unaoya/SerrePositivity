module

public import SerrePositivity.InfinityCategories.F2.Idempotent.WeakInnerAnodyne
public import SerrePositivity.InfinityCategories.Core.InnerAnodyneEquivalence

/-!
概要：指定した元の弱い retract 図式は、強い分裂へ延長でき、その延長空間は可縮。
方針：元の比較への制限の trivial Kan fibration と、元の指定図式上の fiber を使う。
規約：元の弱い全図式を厳密に回収する。既に指定した全 Idem 図式の分裂とは区別する。
使われ方：HTT 4.4.5.6、ホモトピー圏の retract と coherent 分裂の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.F2.Idempotent

/-- 元の弱い retract 添字への制限そのものは、任意の quasicategory に対して trivial Kan。 -/
lemma weakComparisonRestriction_trivialKanFibration (X : SSet.{u}) [Quasicategory X] :
    TrivialKanFibration ((pre weakComparison).app X) :=
  trivialKanFibration_pre_of_innerAnodyne weakComparison weakComparison_innerAnodyne X

/-- 元の弱い全 retract 図式を固定した、強い分裂への元の延長の空間。 -/
def weakDiagramExtensionSpace {X : SSet.{u}} (d : WeakRetractionDiagram X) : SSet.{u} :=
  vertexFiber ((pre weakComparison).app X) (functorVertex d)

/-- 元の弱い全図式を固定した強い分裂への延長空間は可縮な Kan 複体。 -/
lemma weakDiagramExtensionSpace_isContractibleKan {X : SSet.{u}} [Quasicategory X]
    (d : WeakRetractionDiagram X) : IsContractibleKan (weakDiagramExtensionSpace d) := by
  have := weakComparisonRestriction_trivialKanFibration X
  exact vertexFiber_isContractibleKan _ _

/-- 元の弱い全 retract 図式は、同じ制限で厳密に回収される強い全図式へ延長できる。 -/
lemma weakDiagram_extension_exists {X : SSet.{u}} [Quasicategory X]
    (d : WeakRetractionDiagram X) : ∃ s : SplitShape ⟶ X, weakComparison ≫ s = d := by
  have := weakComparison_innerAnodyne.{u} (terminal.from X)
    (InnerFibration.mem (q := terminal.from X))
  have sq : CommSq d weakComparison (terminal.from X) (terminal.from SplitShape) :=
    ⟨terminal.hom_ext _ _⟩
  exact ⟨sq.lift, sq.fac_left⟩

/-- 元の弱い retract は、元の全図式を保つ coherent な冪等図式の強い分裂を与える。 -/
lemma weakDiagram_strongSplitting_exists {X : SSet.{u}} [Quasicategory X]
    (d : WeakRetractionDiagram X) :
    ∃ (e : CoherentIdempotent X) (s : StrongSplitting e), s.weakDiagram = d := by
  obtain ⟨s, hs⟩ := weakDiagram_extension_exists d
  exact ⟨idemInclusion ≫ s, ⟨s, rfl⟩, hs⟩

end SerrePositivity.InfinityCategories.F2.Idempotent
