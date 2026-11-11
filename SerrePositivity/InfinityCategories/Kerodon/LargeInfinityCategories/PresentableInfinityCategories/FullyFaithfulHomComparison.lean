module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.HomComparisonComponent
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.FunctorEdgePointwise
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.InvertibleEdgeLifting

/-!
概要：充満忠実な関手の元の全共変 Hom 比較は全関手同型を与える。
方針：同じ元の射を表す一つの辺と、全評価成分の可逆性の判定を使う。
規約：指定された全比較を順射として保持。値ごとの別の同型へ置換しない。
使われ方：同値による compact 性の輸送。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-- 元の関手圏の射は、指定された全評価成分が可逆なら可逆。 -/
lemma functorHom_isIso_of_components {C X : SSet.{u}} [Quasicategory X] {F G : C ⟶ X}
    (t : (HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F) : hoFunctor.obj ((ihom C).obj X)) ⟶
      HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex G))
    (ht : ∀ c : C _⦋0⦌, IsIso ((hoFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := X) c)).toFunctor.map t)) :
    IsIso t := by
  obtain ⟨e, he⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.homotopyCategory_homMk_surjective (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex G) t
  have h : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge e := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.isInvertibleEdge_iff_evaluateFunctorAt e).mpr (by
    intro c
    change IsIso ((hoFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := X) c)).toFunctor.map
      (SSet.Truncated.HomotopyCategory.homMk e))
    rw [he]
    exact ht c)
  change IsIso (SSet.Truncated.HomotopyCategory.homMk e) at h
  rwa [he] at h

/-- 元の充満忠実関手について、定義済みの全共変 Hom 比較そのものが可逆。 -/
lemma covariantHomComparison_isIso {C E : SSet.{u}} [Quasicategory C] [Quasicategory E]
    (G : C ⟶ E) (hG : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful G) (x : C _⦋0⦌) :
    IsIso (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.covariantHomComparison G x) := by
  apply functorHom_isIso_of_components
  rintro ⟨y⟩
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.covariantHomComparison_component_isIso_iff G x y).mpr (hG x y)

/-- 同じ全比較を順方向の射とする、充満忠実関手の全共変 Hom 同型。 -/
def covariantHomComparisonIso {C E : SSet.{u}} [Quasicategory C] [Quasicategory E]
    (G : C ⟶ E) (hG : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful G) (x : C _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.covariantRepresentableInfinity x)
      ((SSet.uliftFunctor.{u + 1, u}).map G ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.covariantRepresentableInfinity (G.app (Opposite.op ⦋0⦌) x)) := by
  have := covariantHomComparison_isIso G hG x
  exact asIso (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.covariantHomComparison G x)

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
