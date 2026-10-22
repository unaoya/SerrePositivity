module

public import SerrePositivity.InfinityCategories.F2.Presentable.HomComparisonComponent
public import SerrePositivity.InfinityCategories.Core.FunctorEdgePointwise
public import SerrePositivity.InfinityCategories.Core.InvertibleEdgeLifting

/-!
概要：充満忠実な関手の元の全共変 Hom 比較は全関手同型を与える。
方針：同じ元の射を表す一つの辺と、全評価成分の可逆性の判定を使う。
規約：指定された全比較を順射として保持。値ごとの別の同型へ置換しない。
使われ方：同値による compact 性の輸送。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable

/-- 元の関手圏の射は、指定された全評価成分が可逆なら可逆。 -/
lemma functorHom_isIso_of_components {C X : SSet.{u}} [Quasicategory X] {F G : C ⟶ X}
    (t : (HomotopyCategory.mk (functorVertex F) : hoFunctor.obj ((ihom C).obj X)) ⟶
      HomotopyCategory.mk (functorVertex G))
    (ht : ∀ c : C _⦋0⦌, IsIso ((hoFunctor.map (evaluateFunctorAt (Y := X) c)).toFunctor.map t)) :
    IsIso t := by
  obtain ⟨e, he⟩ := homotopyCategory_homMk_surjective (functorVertex F) (functorVertex G) t
  have h : IsInvertibleEdge e := (isInvertibleEdge_iff_evaluateFunctorAt e).mpr (by
    intro c
    change IsIso ((hoFunctor.map (evaluateFunctorAt (Y := X) c)).toFunctor.map
      (SSet.Truncated.HomotopyCategory.homMk e))
    rw [he]
    exact ht c)
  change IsIso (SSet.Truncated.HomotopyCategory.homMk e) at h
  rwa [he] at h

/-- 元の充満忠実関手について、定義済みの全共変 Hom 比較そのものが可逆。 -/
lemma covariantHomComparison_isIso {C E : SSet.{u}} [Quasicategory C] [Quasicategory E]
    (G : C ⟶ E) (hG : IsFullyFaithful G) (x : C _⦋0⦌) :
    IsIso (covariantHomComparison G x) := by
  apply functorHom_isIso_of_components
  rintro ⟨y⟩
  exact (covariantHomComparison_component_isIso_iff G x y).mpr (hG x y)

/-- 同じ全比較を順方向の射とする、充満忠実関手の全共変 Hom 同型。 -/
def covariantHomComparisonIso {C E : SSet.{u}} [Quasicategory C] [Quasicategory E]
    (G : C ⟶ E) (hG : IsFullyFaithful G) (x : C _⦋0⦌) :
    FunctorIso (covariantRepresentableInfinity x)
      ((SSet.uliftFunctor.{u + 1, u}).map G ≫
        covariantRepresentableInfinity (G.app (Opposite.op ⦋0⦌) x)) := by
  have := covariantHomComparison_isIso G hG x
  exact asIso (covariantHomComparison G x)

end SerrePositivity.InfinityCategories.F2.Presentable
