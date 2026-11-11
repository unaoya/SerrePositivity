module

public import SerrePositivity.InfinityCategories.Project.FilteredExchange.IntervalReplacementKanComparison
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.KanSpecifiedPathLift

/-!
概要：通常の区間内部 Hom に値を持つ指定 path の全族を Kan fibration に沿って持ち上げる。
方針：Kan 標的の可逆 path 包含の逆を使い、同じ指定経路の持ち上げを適用する。
規約：底の全 path と指定端点を厳密に保持。使われ方：実 fiber 比較の切断への移送。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
open SSet.modelCategoryQuillen
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {E B T : SSet.{u}} [KanComplex E] [KanComplex B]
  (p : E ⟶ B) [HomotopicalAlgebra.Fibration p] (j : Fin 2)

/-- Kan 標的では、可逆 path 包含の逆も元の指定端点を保つ。 -/
lemma equivalencePathInclusion_inv_endpoint :
    (asIso (equivalencePathι B)).inv ≫ equivalencePathEndpoint B j =
      (intervalEndpointNatTrans j).app B := by
  change (asIso (equivalencePathι B)).inv ≫
    (asIso (equivalencePathι B)).hom ≫ (intervalEndpointNatTrans j).app B = _
  rw [Iso.inv_hom_id_assoc]

variable (a : T ⟶ E) (h : T ⟶ (ihom (Δ[1] : SSet.{u})).obj B)
  (ha : h ≫ (intervalEndpointNatTrans j).app B = a ≫ p)

/-- 指定した通常の区間 path 全体を、入力した端点から持ち上げる。 -/
def kanSpecifiedIntervalLift : T ⟶ equivalencePath E :=
  HomotopyLimits.kanSpecifiedPathLift p j a (h ≫ (asIso (equivalencePathι B)).inv)
    (by rw [Category.assoc, equivalencePathInclusion_inv_endpoint, ha])

/-- 持ち上げは、底の元の全区間 path に厳密に射影する。 -/
lemma kanSpecifiedIntervalLift_projection :
    kanSpecifiedIntervalLift p j a h ha ≫ equivalencePathMap p ≫ equivalencePathι B = h := by
  rw [← Category.assoc, kanSpecifiedIntervalLift,
    HomotopyLimits.kanSpecifiedPathLift_projection, Category.assoc]
  change h ≫ (asIso (equivalencePathι B)).inv ≫ (asIso (equivalencePathι B)).hom = h
  rw [Iso.inv_hom_id, Category.comp_id]

/-- 指定した端点は持ち上げによって動かない。 -/
lemma kanSpecifiedIntervalLift_endpoint :
    kanSpecifiedIntervalLift p j a h ha ≫ equivalencePathEndpoint E j = a :=
  HomotopyLimits.kanSpecifiedPathLift_endpoint _ _ _ _ _

/-- 反対の端点も、元の底の path の反対の端点へ厳密に写る。 -/
lemma kanSpecifiedIntervalLift_other_endpoint :
    (kanSpecifiedIntervalLift p j a h ha ≫ equivalencePathEndpoint E j.rev) ≫ p =
      h ≫ (intervalEndpointNatTrans j.rev).app B := by
  rw [kanSpecifiedIntervalLift, HomotopyLimits.kanSpecifiedPathLift_other_endpoint,
    Category.assoc, equivalencePathInclusion_inv_endpoint]

end SerrePositivity.InfinityCategories.F2
