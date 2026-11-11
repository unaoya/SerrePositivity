module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianEdge
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：cocartesian な辺による輸送を持つ inner fibration。
方針：各基底の辺の始点を指定して cocartesian な持ち上げの存在を要求する。
規約：圏の値を持つ関手への置換や straightening は使わない。
使われ方：Kerodon Definition 5.1.4.1（Tag 01UA）、Proposition 7.1.6.13（Tag 02XB） の錐の輸送。

対応節は Kerodon 5.1（Tag 01T1）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations

/-- 概要：cocartesian fibration は各基底の辺に始点指定の cocartesian な持ち上げを持つ inner fibration。
方針：内ホーンの持ち上げ性と cocartesian な辺の存在を保持する。
規約：quasicategory 性は定義に含めない。
使われ方：Kerodon Definition 5.1.4.1（Tag 01UA） の cocartesian fibration。 -/
@[kerodon 01UA]
class CocartesianHornFibration {E B : SSet.{u}} (p : E ⟶ B) : Prop extends InnerFibration p where
  /-- 始点を指定した基底の辺の cocartesian な持ち上げ。 -/
  exists_lift : ∀ (x : E _⦋0⦌) (b : B _⦋0⦌)
    (a : SSet.Truncated.Edge (X := (truncation 2).obj B) (p.app (Opposite.op ⦋0⦌) x) b),
    ∃ (y : E _⦋0⦌) (e : SSet.Truncated.Edge (X := (truncation 2).obj E) x y),
      p.app (Opposite.op ⦋1⦌) e.edge = a.edge ∧ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.HasCocartesianHornLifting p e

/-- 概要：恒等射に対して全ての辺は cocartesian。
方針：指定された基底の単体をそのまま充填にする。
規約：quasicategory 性は不要。
使われ方：Kerodon §5.1.4（Tag 01U9） の恒等な輸送。 -/
lemma hasCocartesianHornLifting_id {E : SSet.{u}} {x y : E _⦋0⦌}
    (e : SSet.Truncated.Edge (X := (truncation 2).obj E) x y) : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.HasCocartesianHornLifting (𝟙 E) e := by
  intro n σ β _ hw
  exact ⟨β, by simpa only [Category.comp_id] using hw.symm, Category.comp_id _⟩

/-- 概要：恒等射は cocartesian fibration。
方針：基底の辺をそのまま持ち上げる。
規約：quasicategory 性は不要。
使われ方：Kerodon §5.1.4（Tag 01U9） の cocartesian fibration の基本例。 -/
instance cocartesianHornFibration_id (E : SSet.{u}) : CocartesianHornFibration (𝟙 E) where
  mem := by
    intro A B i hi
    exact HasLiftingProperty.of_right_iso _ _
  exists_lift x b a := ⟨b, a, rfl, hasCocartesianHornLifting_id a⟩

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
