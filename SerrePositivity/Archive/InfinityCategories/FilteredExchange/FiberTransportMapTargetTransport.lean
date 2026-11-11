module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.FiberTransportFamily

/-!
概要：元の全作用比較は、同じ実標的証拠の厳密な表示変更で指定値を保持する。
方針：実標的レコードの等式を消去する。
規約：元の指定同型を保持。使われ方：直接普遍比較の実標的表示の回収。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 同じ実標的レコードへの表示変更は、元の全作用比較の指定値を保つ。 -/
lemma fiberTransportFamily_mapIso_heq_of_target_eq {E B K L : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] {a b : B _⦋0⦌} (f : K ⟶ vertexFiber p a)
    (γ : (Δ[1] : SSet.{u}) ⊗ L ⟶ B) (h₁ : prismEndpoint 1 L ≫ γ = SSet.const b)
    (T U V : FiberTransportFamily (b := b) p f γ) (h : U = V) :
    HEq (T.mapIso p f γ h₁ U) (T.mapIso p f γ h₁ V) := by
  subst V
  rfl

end SerrePositivity.InfinityCategories.F2
