module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.DiagonalFiberTransportSquare

/-!
概要：元の輸送族の全対角比較に使う、実 prism と実両端・底を明示する。
方針：元の二係数制限を保持し、prism の端点と射影の自然性を計算する。
規約：元の全実輸送族を保持。使われ方：指定比較の実二 prism 表示と係数制限。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {P E B K L : SSet.{u}} (p : E ⟶ B) [LeftFibration p] {a b : B _⦋0⦌}
  (f : K ⟶ vertexFiber p a) (γ : (Δ[1] : SSet.{u}) ⊗ L ⟶ B)
  (h₀ : prismEndpoint 0 L ≫ γ = SSet.const a)
  (h₁ : prismEndpoint 1 L ≫ γ = SSet.const b)
  (T : FiberTransportFamily (b := b) p f γ) (x : P ⟶ K) (y : P ⟶ L)
local notation "d" => lift x y
local notation "H" => (Δ[1] ◁ d) ≫ T.prism
local notation "v" => y ≫ intervalMappingCurryOfEndpoints γ h₀ h₁

/-- 元の全対角比較の実 prism の始点は、元の同じ実初期値。 -/
lemma fiberTransportDiagonalPrism_start :
    prismEndpoint 0 P ≫ H = (x ≫ f) ≫ vertexFiberι p a := by
  rw [← Category.assoc, prismEndpoint_naturality, Category.assoc, T.start,
    ← Category.assoc, ← Category.assoc, lift_fst, Category.assoc]

/-- 元の全対角比較の実 prism の終点は、元の同じ実終点。 -/
lemma fiberTransportDiagonalPrism_finish :
    prismEndpoint 1 P ≫ H = (lift x y ≫ T.endpoint) ≫ vertexFiberι p b := by
  rw [← Category.assoc, prismEndpoint_naturality, Category.assoc, T.finish]
  rfl

/-- 元の全対角比較の実 prism は、元の同じ全区間を被覆する。 -/
lemma fiberTransportDiagonalPrism_projection : H ≫ p = intervalMappingUncurry v := by
  rw [Category.assoc, T.over_base, ← whiskerLeft_comp_assoc, lift_snd]
  rw [intervalMappingUncurry_precomp, intervalMappingUncurry_curryOfEndpoints]

end SerrePositivity.InfinityCategories.F2
