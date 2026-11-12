module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SpanHomotopyGluing
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.RoofRelativeEvaluation
/-!
概要：指定 fiber の同型表示を使い、境界の評価値と全比較を保つ相対評価を構成する。
方針：fiber 表示の逆で境界を移し、相対評価後に元の表示へ戻す。
規約：評価の包含は同じ同型で共役する。使われ方：任意標的の実 pinched Hom への相対評価。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory MonoidalCategory SSet
open scoped _root_.Simplicial
/-- 同型で表示した fiber への、全境界比較を保つ相対評価。 -/
structure RoofRelativeIsoEvaluation {L K E B Z : SSet.{u}} (p : E ⟶ B) (t : B _⦋0⦌)
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p t ≅ Z) (i : L ⟶ K) (a : K ⟶ E) (g : L ⟶ Z)
    (H : SSet.Homotopy (i ≫ a) (g ≫ (e.inv ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p t)))
    (β : SSet.Homotopy (a ≫ p) (SSet.const t)) where
  value : K ⟶ Z
  value_boundary : i ≫ value = g
  homotopy : SSet.Homotopy a (value ≫ (e.inv ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p t))
  over : homotopy.h ≫ p = β.h
  boundary : (i ▷ (Δ[1] : SSet.{u})) ≫ homotopy.h = H.h
/-- fiber の指定同型表示でも、任意単射上の値と全比較を保つ相対評価が存在する。 -/
lemma roofRelativeIsoEvaluation_nonempty {L K E B Z : SSet.{u}}
    (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] (t : B _⦋0⦌) (e : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p t ≅ Z)
    (i : L ⟶ K) [Mono i] (a : K ⟶ E) (g : L ⟶ Z)
    (H : SSet.Homotopy (i ≫ a) (g ≫ (e.inv ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p t)))
    (β : SSet.Homotopy (a ≫ p) (SSet.const t))
    (hH : H.h ≫ p = (i ▷ (Δ[1] : SSet.{u})) ≫ β.h) :
    Nonempty (RoofRelativeIsoEvaluation p t e i a g H β) := by
  let H' := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stableHomotopyRetarget H rfl (Category.assoc _ _ _).symm
  obtain ⟨R⟩ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofRelativeEvaluation_nonempty p t i a (g ≫ e.inv) H' β hH
  let f := R.evaluation ≫ e.hom
  have hf : i ≫ f = g := by
    dsimp only [f]
    rw [← Category.assoc, R.evaluation_boundary, Category.assoc,
      Iso.inv_hom_id, Category.comp_id]
  have ht : R.evaluation ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p t = f ≫ (e.inv ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p t) := by
    dsimp only [f]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
  let T := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stableHomotopyRetarget R.homotopy rfl ht
  exact ⟨⟨f, hf, T, R.over, R.boundary⟩⟩
end SerrePositivity.InfinityCategories.Project.DerivedCategories
