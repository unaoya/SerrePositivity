module

public import SerrePositivity.InfinityCategories.F2.PointedIntervalTransportPointPrism

/-!
概要：同じ指定一点区間上の実 pointed prism を、元の区間全体の輸送証人へ戻す。
方針：一点因子を忘れる射で元の prism と終点を前合成する。
規約：元の prism・実両端・区間を保持。使われ方：明示した長辺と元の普遍比較の照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {K : SSet.{u + 1}} {x y : SpaceInfinity.{u} _⦋0⦌}
  (a : (Δ[0] : SSet.{u + 1}) ⟶ intervalMappingSpace x y)
  (f : K ⟶ vertexFiber pointedSpaceProjection x) (g : K ⟶ vertexFiber pointedSpaceProjection y)
  (P : (Δ[1] : SSet.{u + 1}) ⊗ K ⟶ PointedSpaceInfinity.{u})
  (h₀ : prismEndpoint 0 K ≫ P = f ≫ vertexFiberι pointedSpaceProjection x)
  (h₁ : prismEndpoint 1 K ≫ P = g ≫ vertexFiberι pointedSpaceProjection y)
  (hp : P ≫ pointedSpaceProjection =
    (Δ[1] ◁ (SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 1)) : K ⟶ Δ[0])) ≫
      intervalMappingUncurry a)

/-- 元の実一点 prism と同じ終点を持つ、元の同じ全区間の輸送証人。 -/
def pointedSingletonPrismFamily :
    FiberTransportFamily (b := y) pointedSpaceProjection f (intervalMappingUncurry a) where
  endpoint := fst K Δ[0] ≫ g
  prism := (Δ[1] ◁ fst K (Δ[0] : SSet.{u + 1})) ≫ P
  start := by
    rw [← Category.assoc, prismEndpoint_naturality, Category.assoc, h₀]
  finish := by
    rw [← Category.assoc, prismEndpoint_naturality, Category.assoc, h₁]
    rfl
  over_base := by
    rw [Category.assoc, hp, ← Category.assoc, ← whiskerLeft_comp]
    have ht : fst K (Δ[0] : SSet.{u + 1}) ≫
        (SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 1)) : K ⟶ Δ[0]) = snd K Δ[0] :=
      stdSimplex.isTerminalObj₀.hom_ext _ _
    rw [ht]

/-- 同じ証人の任意の一点での終点は、元の同じ実終点射そのもの。 -/
lemma pointedSingletonPrismFamily_point_endpoint (v : (Δ[0] : SSet.{u + 1}) _⦋0⦌) :
    lift (𝟙 K) (SSet.const v) ≫ (pointedSingletonPrismFamily a f g P h₀ h₁ hp).endpoint = g := by
  change lift (𝟙 K) (SSet.const v) ≫ (fst K Δ[0] ≫ g) = g
  rw [← Category.assoc, lift_fst, Category.id_comp]

/-- 同じ証人の任意の一点 prism は、元の同じ全係数 prism に厳密に戻る。 -/
lemma pointedSingletonPrismFamily_point_prism (v : (Δ[0] : SSet.{u + 1}) _⦋0⦌) :
    (Δ[1] ◁ lift (𝟙 K) (SSet.const v)) ≫
      (pointedSingletonPrismFamily a f g P h₀ h₁ hp).prism = P := by
  change (Δ[1] ◁ lift (𝟙 K) (SSet.const v)) ≫ (Δ[1] ◁ fst K Δ[0]) ≫ P = P
  rw [← Category.assoc, ← whiskerLeft_comp, lift_fst, whiskerLeft_id, Category.id_comp]

end SerrePositivity.InfinityCategories.F2
