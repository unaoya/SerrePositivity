module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.LiftedIntervalEndpoints

/-!
概要：元の小さい右区間円柱の持ち上げを、標準右区間円柱へ比較する。
方針：直積と標準単体の宇宙同型を合成する。
規約：元の全零端点とパラメーター制限を保持。使われ方：F を元の小さい円柱で使う。

対応節は Kerodon 9.3（Tag 06FR）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories

/-- 元の小さい右区間円柱を、そのまま持ち上げて標準区間へ比較する。 -/
def rightIntervalUniverseShape (A : SSet.{u}) :
    (SSet.uliftFunctor.{u + 1, u}).obj (A ⊗ Δ[1]) ⟶
      (SSet.uliftFunctor.{u + 1, u}).obj A ⊗ (Δ[1] : SSet.{u + 1}) :=
  (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftTensorIso.{u, u + 1} A Δ[1]).hom ≫
    ((SSet.uliftFunctor.{u + 1, u}).obj A ◁
      (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftStdSimplexIso.{u, u + 1} 1).hom)

/-- この元の円柱の全形状比較は、実際の同型。 -/
instance rightIntervalUniverseShape_isIso (A : SSet.{u}) :
    IsIso (rightIntervalUniverseShape A) := by
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

/-- 逆比較でも元の全零端点は厳密に回収される。 -/
lemma rightIntervalUniverseShape_inv_zero (A : SSet.{u}) :
    SSet.ι₀ ≫ inv (rightIntervalUniverseShape A) =
      (SSet.uliftFunctor.{u + 1, u}).map (SSet.ι₀ : A ⟶ A ⊗ Δ[1]) := by
  calc
    _ = ((SSet.uliftFunctor.{u + 1, u}).map SSet.ι₀ ≫ rightIntervalUniverseShape A) ≫
        inv (rightIntervalUniverseShape A) := by rw [rightIntervalUniverseShape_zero]
    _ = _ := by rw [Category.assoc, IsIso.hom_inv_id, Category.comp_id]

/-- 逆比較も元の全パラメーター制限と厳密に可換。 -/
lemma rightIntervalUniverseShape_inv_naturality {A B : SSet.{u}} (f : A ⟶ B) :
    ((SSet.uliftFunctor.{u + 1, u}).map f ▷ (Δ[1] : SSet.{u + 1})) ≫
      inv (rightIntervalUniverseShape B) = inv (rightIntervalUniverseShape A) ≫
        (SSet.uliftFunctor.{u + 1, u}).map (f ▷ (Δ[1] : SSet.{u})) := by
  apply (cancel_mono (rightIntervalUniverseShape B)).mp
  simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id,
    rightIntervalUniverseShape_naturality]
  simp only [← Category.assoc, IsIso.inv_hom_id, Category.id_comp]

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
