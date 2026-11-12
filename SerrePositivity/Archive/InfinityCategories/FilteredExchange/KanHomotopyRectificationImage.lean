module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.KanHomotopyRectification
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.HomotopyIsoWhiskering
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.UnitComparisonFiberForwardData

/-!
概要：指定ホモトピーによる厳密化の全円柱と指定同型は、底で元の指定値へ厳密に写る。
方針：可逆 path の普遍円柱の自然性と指定持ち上げの射影を合成する。
規約：元の円柱の類を選び直さない。使われ方：実模型比較の二脚の底の整合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory SSet
open SSet.modelCategoryQuillen
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {E B T : SSet.{u}} [KanComplex E] [KanComplex B]
  (p : E ⟶ B) [HomotopicalAlgebra.Fibration p]
  (a : T ⟶ E) (b : T ⟶ B) (H : SSet.Homotopy (a ≫ p) b)

/-- 可逆 path の普遍円柱は、元の射の全単体で後合成と交換する。 -/
lemma equivalencePathHomotopy_map :
    (equivalencePathHomotopy E).h ≫ p =
      (equivalencePathMap p ▷ (Δ[1] : SSet.{u})) ≫ (equivalencePathHomotopy B).h := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro x
  rfl

/-- 厳密化に用いた持ち上げの全円柱の像は、底の元の指定ホモトピー。 -/
lemma kanHomotopyRectificationHomotopy_image :
    (kanHomotopyRectificationHomotopy p a b H).h ≫ p = H.h := by
  change ((kanHomotopyRectificationPath p a b H ▷ (Δ[1] : SSet.{u})) ≫
    (equivalencePathHomotopy E).h) ≫ p = H.h
  rw [Category.assoc, equivalencePathHomotopy_map, ← Category.assoc,
    ← MonoidalCategory.comp_whiskerRight, kanHomotopyRectificationPath_projection,
    homotopyEquivalencePath_homotopy]

/-- 指定同型の像も、明示した終点の式による補正後は元の指定円柱の同型に一致。 -/
lemma kanHomotopyRectificationIso_image :
    functorIsoOfEq ((kanHomotopyRectificationIso p a b H).postcomp p) rfl
      (kanHomotopyRectification_over p a b H) = functorIsoOfSimplicialHomotopy H := by
  rw [kanHomotopyRectificationIso, ← homotopyIso_postcomp]
  exact functorIsoOfEq_of_homotopy_h_eq
    (functorHomotopyPostcomp (kanHomotopyRectificationHomotopy p a b H) p) H _ _ rfl rfl rfl
    (kanHomotopyRectification_over p a b H) (kanHomotopyRectificationHomotopy_image p a b H)

end SerrePositivity.InfinityCategories.F2
