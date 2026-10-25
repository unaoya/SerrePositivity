module

public import
SerrePositivity.InfinityCategories.F2.FilteredExchange.RelativeExtensionFiberWitnessRestriction
public import
SerrePositivity.InfinityCategories.F2.FilteredExchange.RelativeExtensionFiberWitnessIdentity

/-!
概要：固定初期図式内にある実終点では、元の全延長の指定比較は恒等である。
方針：初期図式そのものへ制限し、同じ実延長となる指定比較を消去する。
規約：元の指定比較を保持。使われ方：四角形の下二頂点像の恒等性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 固定した初期図式内で評価する元の二延長の指定比較は、同じ実値の恒等同型。 -/
lemma relativeExtensionFiberEndpoint_witnessIso_eq_refl_of_initial
    {D I C E B : SSet.{u}} (p : E ⟶ B) [LeftFibration p] (β : D ⟶ B)
    (i : I ⟶ D) (hi : leftAnodyneExtensions i) (v : I ⟶ E) (hv : v ≫ p = i ≫ β)
    (j : C ⟶ D) (k : C ⟶ I) (hk : k ≫ i = j)
    (z : B _⦋0⦌) (hz : j ≫ β = SSet.const z)
    (W W' : D ⟶ E) (hW : W ≫ p = β) (hW' : W' ≫ p = β)
    (hWi : i ≫ W = v) (hWi' : i ≫ W' = v)
    (g : C ⟶ vertexFiber p z) (hg : j ≫ W = g ≫ vertexFiberι p z)
    (hg' : j ≫ W' = g ≫ vertexFiberι p z) :
    relativeExtensionFiberEndpoint_witnessIso p β i hi v hv j z hz
      W W' hW hW' hWi hWi' g g hg hg' = Iso.refl _ := by
  have h := relativeExtensionFiberEndpoint_witnessIso_restriction p β i hi v hv i
    (𝟙 I) (𝟙 I) (leftAnodyneExtensions.id_mem I) rfl j k hk z hz
    W W' hW hW' hWi hWi' g g hg hg'
  exact h.trans (relativeExtensionFiberEndpoint_witnessIso_eq_refl_of_eq p _ _
    (leftAnodyneExtensions.id_mem I) _ _ _ z _ _ _ _ _ _ _ g _ _ (hWi.trans hWi'.symm))

end SerrePositivity.InfinityCategories.F2
