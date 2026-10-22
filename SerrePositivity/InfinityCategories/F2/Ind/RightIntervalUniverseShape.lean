module

public import SerrePositivity.InfinityCategories.F2.Ind.LiftedIntervalEndpoints

/-!
概要：元の小さい右区間円柱の持ち上げを、標準右区間円柱へ比較する。
方針：直積と標準単体の宇宙同型を合成する。
規約：元の全零端点とパラメーター制限を保持。使われ方：F を元の小さい円柱で使う。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind

/-- 元の小さい右区間円柱を、そのまま持ち上げて標準区間へ比較する。 -/
def rightIntervalUniverseShape (A : SSet.{u}) :
    (SSet.uliftFunctor.{u + 1, u}).obj (A ⊗ Δ[1]) ⟶
      (SSet.uliftFunctor.{u + 1, u}).obj A ⊗ (Δ[1] : SSet.{u + 1}) :=
  (HomotopyLimits.uliftTensorIso.{u, u + 1} A Δ[1]).hom ≫
    ((SSet.uliftFunctor.{u + 1, u}).obj A ◁
      (HomotopyLimits.uliftStdSimplexIso.{u, u + 1} 1).hom)

/-- この元の円柱の全形状比較は、実際の同型。 -/
instance rightIntervalUniverseShape_isIso (A : SSet.{u}) : IsIso (rightIntervalUniverseShape A) := by
  dsimp only [rightIntervalUniverseShape]
  infer_instance

/-- パラメーターの制限も、元の小さい円柱の全比較で保たれる。 -/
lemma rightIntervalUniverseShape_naturality {A B : SSet.{u}} (f : A ⟶ B) :
    (SSet.uliftFunctor.{u + 1, u}).map (f ▷ (Δ[1] : SSet.{u})) ≫
      rightIntervalUniverseShape B = rightIntervalUniverseShape A ≫
        ((SSet.uliftFunctor.{u + 1, u}).map f ▷ (Δ[1] : SSet.{u + 1})) := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro x
  rfl

/-- 元の零端点は、同じ全零端点に厳密に送られる。 -/
lemma rightIntervalUniverseShape_zero (A : SSet.{u}) :
    (SSet.uliftFunctor.{u + 1, u}).map (SSet.ι₀ : A ⟶ A ⊗ Δ[1]) ≫
      rightIntervalUniverseShape A = SSet.ι₀ := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro x
  rfl

end SerrePositivity.InfinityCategories.F2.Ind
