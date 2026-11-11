module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.FiberTransportFamilyNaturality

/-!
概要：元の全輸送の一点制限を、同じ実始点・実終点・底の区間で記述する。
方針：prism の端点制限の自然性と tensor の射影を計算する。
規約：元の実 prism と全初期値を保持。使われ方：元の比較と native 証拠の照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {E B K L : SSet.{u}} (p : E ⟶ B) {a b : B _⦋0⦌}
  (f : K ⟶ vertexFiber p a) (γ : (Δ[1] : SSet.{u}) ⊗ L ⟶ B)
  (T : FiberTransportFamily (b := b) p f γ) (l : L _⦋0⦌)
local notation "r" => lift (𝟙 K) (SSet.const l)
local notation "P" => (Δ[1] ◁ r) ≫ FiberTransportFamily.prism T

/-- 元の一点実 prism の始点は、元の全初期値そのもの。 -/
lemma fiberTransportFamily_point_prism_start :
    prismEndpoint 0 K ≫ P = f ≫ vertexFiberι p a := by
  rw [← Category.assoc, prismEndpoint_naturality, Category.assoc, T.start]
  simp only [← Category.assoc, lift_fst, Category.id_comp]

/-- 元の一点実 prism の終点は、元の実終点の同じ一点制限そのもの。 -/
lemma fiberTransportFamily_point_prism_finish :
    prismEndpoint 1 K ≫ P = (r ≫ T.endpoint) ≫ vertexFiberι p b := by
  rw [← Category.assoc, prismEndpoint_naturality, Category.assoc, T.finish, Category.assoc]

/-- 元の一点実 prism は、元の全区間の同じ一点制限を被覆する。 -/
lemma fiberTransportFamily_point_prism_projection :
    P ≫ p = (Δ[1] ◁ (SSet.const l : K ⟶ L)) ≫ γ := by
  rw [Category.assoc, T.over_base, ← whiskerLeft_comp_assoc, lift_snd]

end SerrePositivity.InfinityCategories.F2
