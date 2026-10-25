module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.RelativeExtensionPost
public import
SerrePositivity.InfinityCategories.F2.FilteredExchange.RelativeExtensionFiberEndpointEvaluation

/-!
概要：元の全延長の後合成は、同じ終点の fiber 内の評価と厳密に可換する。
方針：uncurry と fiber 包含後に戻して、元の全延長の後合成を計算する。
規約：底・初期値・全係数を保持。使われ方：指定比較の後合成自然性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
open HomotopyLimits

/-- 全相対延長の後合成と、元の実終点の fiber 評価は厳密に可換する。 -/
lemma relativeExtensionFiberEndpoint_post {A D C E F B : SSet.{u}}
    (p : E ⟶ B) (q : F ⟶ B) (f : E ⟶ F) (hf : f ≫ q = p)
    (b : A ⟶ B) (i : D ⟶ A) (v : D ⟶ E) (hv : v ≫ p = i ≫ b)
    (j : C ⟶ A) (z : B _⦋0⦌) (hj : j ≫ b = SSet.const z) :
    relativeExtensionPost p q f hf b i v hv ≫
      relativeExtensionFiberEndpoint q b i (v ≫ f)
        (relativeExtensionPost_initial_base p q f hf b i v hv) j z hj =
      relativeExtensionFiberEndpoint p b i v hv j z hj ≫
        (ihom C).map (vertexFiberMap p q f hf z) := by
  apply uncurry_injective
  apply vertexFiber_hom_ext q z
  rw [uncurry_natural_left, Category.assoc, relativeExtensionFiberEndpoint_uncurry_ι,
    uncurry_natural_right, Category.assoc, vertexFiberMap_ι,
    ← Category.assoc, relativeExtensionFiberEndpoint_uncurry_ι,
    ← relativeFunctorUncurry_naturality]
  rw [← Category.assoc (relativeExtensionPost p q f hf b i v hv),
    relativeExtensionPost_ι, Category.assoc, relativeFunctorPost_pre,
    ← Category.assoc, relativeFunctorUncurry_post]

end SerrePositivity.InfinityCategories.F2
