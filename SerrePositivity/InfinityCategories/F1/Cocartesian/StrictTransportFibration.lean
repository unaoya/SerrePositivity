module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.UnderMapMono
public import SerrePositivity.InfinityCategories.F1.Cocartesian.SectionsRestrictionLifting
public import SerrePositivity.InfinityCategories.F2.CoreIsofibration

/-!
概要：薄い底上の元の strict transport の遷移は、同値の相対持ち上げを持つ。
方針：元の undercategory の単射を section の制限へ渡し、内部 Hom と core に移す。
規約：遷移の同値性を仮定しない。
使われ方：一次元セルの厳密な変換空間の pullback を導来比較に使う。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
namespace SerrePositivity.InfinityCategories

/-- 薄い底での同じ strict transport の遷移は、単射な同値を右に持ち上げる。 -/
lemma kanEquivalenceLifting_kanCocartesianStrictTransportMap_of_thin
    {C : Type u} [Category.{u} C] [Quiver.IsThin C] {E : SSet.{u}}
    (p : E ⟶ nerve C) [CocartesianFibration p] {c d : C} (f : c ⟶ d) :
    F1B.KanEquivalenceLifting (kanCocartesianStrictTransportMap p f) := by
  let i : Over.mk (nerveMap (Under.forget d)) ⟶
      Over.mk (nerveMap (Under.forget c)) :=
    Over.homMk (nerveUnderMap f) (nerveUnderMap_projection f)
  haveI : Mono i.left := kanCocartesianUnderMap_mono_of_thin f
  intro A B j hj he
  exact kanEquivalenceLifting_kanCocartesianSectionsPre p i j hj he

/-- 同じ有限単体上の元の輸送遷移は、追加仮定なしに単射な同値を右に持ち上げる。 -/
lemma kanEquivalenceLifting_kanCocartesianStrictTransportMap_finite
    (n : ℕ) {E : SSet.{u}} (p : E ⟶ nerve (ULift.{u} (Fin (n + 1))))
    [CocartesianFibration p] {c d : ULift.{u} (Fin (n + 1))} (f : c ⟶ d) :
    F1B.KanEquivalenceLifting (kanCocartesianStrictTransportMap p f) :=
  kanEquivalenceLifting_kanCocartesianStrictTransportMap_of_thin p f

/-- 同じ輸送遷移の後合成は、任意の始域を持つ全内部 Hom で同値を右に持ち上げる。 -/
lemma kanEquivalenceLifting_kanCocartesianStrictTransportPostHom
    {C : Type u} [Category.{u} C] [Quiver.IsThin C] {E : SSet.{u}}
    (p : E ⟶ nerve C) [CocartesianFibration p] {c d : C} (f : c ⟶ d) (A : SSet.{u}) :
    F1B.KanEquivalenceLifting ((ihom A).map (kanCocartesianStrictTransportMap p f)) :=
  F1B.KanEquivalenceLifting.internalHom
    (kanEquivalenceLifting_kanCocartesianStrictTransportMap_of_thin p f) A

/-- 同じ後合成の core 上の実際の作用は Kan fibration。 -/
lemma core_kanCocartesianStrictTransportPostHom_fibration
    {C : Type u} [Category.{u} C] [Quiver.IsThin C] {E : SSet.{u}}
    (p : E ⟶ nerve C) [CocartesianFibration p] {c d : C} (f : c ⟶ d) (A : SSet.{u}) :
    Fibration (quasicategoryCoreMap ((ihom A).map (kanCocartesianStrictTransportMap p f))) :=
  F2.coreMap_fibration_of_kanEquivalenceLifting _
    (kanEquivalenceLifting_kanCocartesianStrictTransportPostHom p f A)

end SerrePositivity.InfinityCategories
