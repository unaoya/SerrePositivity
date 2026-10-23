module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.RelativeExtensionUniversalPrismEndpoint
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.RelativeUncurryPointVertices

/-!
概要：全 prism 選択空間の元の実頂点で普遍評価すると、元の実 prism と fiber 終点を回収する。
方針：相対 uncurry の一点評価と同じ実係数射を使う。
規約：元の実 prism と終点を保持。使われ方：全第一辺の自然性を元の二辺比較へ戻す。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {K E B : SSet.{u}} (p : E ⟶ B) (β : (Δ[1] : SSet.{u}) ⊗ K ⟶ B)
  (v : K ⟶ E) (hv : v ≫ p = prismEndpoint 0 K ≫ β)
  (W : (Δ[1] : SSet.{u}) ⊗ K ⟶ E) (hp : W ≫ p = β) (hs : prismEndpoint 0 K ≫ W = v)
local notation "q" => relativeFunctorExtensionSpaceVertexEquiv p β (prismEndpoint 0 K) v hv
  (Subtype.mk W (And.intro hp hs))
local notation "t" => lift (𝟙 K) (SSet.const q)

/-- 元の実頂点で全普遍 prism を制限すると、同じ元の実 prism を厳密に回収する。 -/
lemma relativeExtensionUniversalPrism_at_vertex :
    (Δ[1] ◁ t) ≫ relativeExtensionUniversalPrism p β v hv = W := by
  rw [relativeExtensionUniversalPrism, ← Category.assoc]
  have hn : (Δ[1] ◁ t) ≫ (α_ Δ[1] K _).inv =
      lift (𝟙 ((Δ[1] : SSet.{u}) ⊗ K)) (SSet.const q) := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro k
    rfl
  rw [hn]
  apply functorVertex_injective
  exact congrArg Subtype.val (relativeFunctorUncurry_point_vertex p β
    (relativeFunctorExtensionSpaceι p β (prismEndpoint 0 K) v hv) q)

/-- 元の実頂点の全 fiber 終点は、元の同じ指定終点射そのもの。 -/
lemma relativeExtensionUniversalPrismEndpoint_at_vertex
    (z : B _⦋0⦌) (hz : prismEndpoint 1 K ≫ β = SSet.const z)
    (g : K ⟶ vertexFiber p z) (hg : prismEndpoint 1 K ≫ W = g ≫ vertexFiberι p z) :
    t ≫ relativeExtensionUniversalPrismEndpoint p β v hv z hz = g := by
  apply vertexFiber_hom_ext p z
  rw [Category.assoc, ← relativeExtensionUniversalPrism_finish, ← Category.assoc,
    ← prismEndpoint_naturality, Category.assoc,
    relativeExtensionUniversalPrism_at_vertex p β v hv W hp hs]
  exact hg

end SerrePositivity.InfinityCategories.F2
