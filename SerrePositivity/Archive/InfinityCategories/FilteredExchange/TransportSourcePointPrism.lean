module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.FiberTransportFamilyNaturality

/-!
概要：元の輸送の初期値制限後の実一点 prism を、元の全初期値の同じ実制限へ戻す。
方針：二段の全係数制限を tensor の合成則で計算する。
規約：元の実 prism を保持。使われ方：native 長辺比較の第二の実 prism の照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 元の実 prism の初期値制限後の一点制限は、元の初期値と点による同じ実制限。 -/
lemma fiberTransportFamily_precomposeSource_point_prism {E B K K' L : SSet.{u}}
    (p : E ⟶ B) {a b : B _⦋0⦌} (f : K ⟶ vertexFiber p a)
    (γ : (Δ[1] : SSet.{u}) ⊗ L ⟶ B)
    (T : FiberTransportFamily (b := b) p f γ) (r : K' ⟶ K) (l : L _⦋0⦌) :
    (Δ[1] ◁ lift (𝟙 K') (SSet.const l)) ≫ (T.precomposeSource r).prism =
      (Δ[1] ◁ lift r (SSet.const l)) ≫ T.prism := by
  change (Δ[1] ◁ lift (𝟙 K') (SSet.const l)) ≫ (Δ[1] ◁ (r ▷ L)) ≫ T.prism = _
  rw [← Category.assoc, ← whiskerLeft_comp]
  have hj : lift (𝟙 K') (SSet.const l) ≫ (r ▷ L) = lift r (SSet.const l) := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro k
    rfl
  rw [hj]

end SerrePositivity.InfinityCategories.F2
