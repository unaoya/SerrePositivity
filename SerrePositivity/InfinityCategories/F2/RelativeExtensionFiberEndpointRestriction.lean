module

public import SerrePositivity.InfinityCategories.F2.RelativeExtensionRestrictionEvaluation
public import SerrePositivity.InfinityCategories.F2.RelativeExtensionFiberEndpointEvaluation

/-!
概要：元の全延長の制限は、同じ実終点の fiber 評価と厳密に可換する。
方針：包含後の全評価へ戻し、同じ終点の正方形を元の実射で計算する。
規約：初期値・底・実終点を保持。使われ方：元の二つの prism 比較の表示を照合する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 同じ実終点を保つ延長空間の制限は、元の fiber 終点の全評価と可換する。 -/
lemma relativeExtensionFiberEndpoint_restriction {A D A' D' C E B : SSet.{u}}
    (p : E ⟶ B) (b : A ⟶ B) (i : D ⟶ A) (v : D ⟶ E)
    (hv : v ≫ p = i ≫ b) (h : A' ⟶ A) (k : D' ⟶ D) (i' : D' ⟶ A')
    (hs : i' ≫ h = k ≫ i) (j : C ⟶ A) (j' : C ⟶ A') (hsj : j' ≫ h = j)
    (z : B _⦋0⦌) (hj : j ≫ b = SSet.const z) :
    relativeExtensionRestriction p b i v hv h k i' hs ≫
      relativeExtensionFiberEndpoint p (h ≫ b) i' (k ≫ v)
        (by rw [Category.assoc, hv, ← Category.assoc, ← hs, Category.assoc]) j' z
        (by rw [← Category.assoc, hsj, hj]) =
      relativeExtensionFiberEndpoint p b i v hv j z hj := by
  apply uncurry_injective
  apply vertexFiber_hom_ext p z
  rw [uncurry_natural_left, Category.assoc, relativeExtensionFiberEndpoint_uncurry_ι,
    relativeExtensionFiberEndpoint_uncurry_ι, ← relativeFunctorUncurry_naturality]
  rw [← Category.assoc (relativeExtensionRestriction p b i v hv h k i' hs),
    relativeFunctorUncurry_pre, relativeExtensionRestriction_uncurry, relativeFunctorUncurry_pre]
  rw [← Category.assoc, ← MonoidalCategory.comp_whiskerRight, hsj]

end SerrePositivity.InfinityCategories.F2
