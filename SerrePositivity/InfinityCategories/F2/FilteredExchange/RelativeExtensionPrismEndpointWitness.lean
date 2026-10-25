module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.RelativeExtensionPrismRestriction
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.RelativePrismInitialEndpoint

/-!
概要：全延長比較を辺に制限した始点像・実終点像は、同じ全図式の指定終点比較。
方針：表示変更の同型を除き、同じ可縮な延長空間の端点像へ戻す。
規約：指定値と実端点を保持。使われ方：全四角形の比較の三辺への制限。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {D I E B A : SSet.{u}} (p : E ⟶ B) [LeftFibration p] (β : D ⟶ B)
  (i : I ⟶ D) (hi : leftAnodyneExtensions i) (v : I ⟶ E) (hv : v ≫ p = i ≫ β)
  (W W' : D ⟶ E) (hW : W ≫ p = β) (hW' : W' ≫ p = β)
  (hWi : i ≫ W = v) (hWi' : i ≫ W' = v) (r : (Δ[1] : SSet.{u}) ⊗ A ⟶ D)
local notation "η" => relativeExtensionPrismRestrictionIso p β i hi v hv
  W W' hW hW' hWi hWi' r

/-- 同じ全延長比較の辺制限の指定始点像は、元の全図式の同じ指定終点比較。 -/
lemma relativeExtensionPrism_initial_eq_witness (z : B _⦋0⦌)
    (hz : (prismEndpoint 0 A ≫ r) ≫ β = SSet.const z)
    (g g' : A ⟶ vertexFiber p z)
    (hg : (prismEndpoint 0 A ≫ r) ≫ W = g ≫ vertexFiberι p z)
    (hg' : (prismEndpoint 0 A ≫ r) ≫ W' = g' ≫ vertexFiberι p z) :
    relativePrismInitialEndpointIso p (r ≫ β) z
      ((Category.assoc (prismEndpoint 0 A) r β).symm.trans hz)
      (r ≫ W) (r ≫ W') (by rw [Category.assoc, hW]) (by rw [Category.assoc, hW']) g g'
      ((Category.assoc (prismEndpoint 0 A) r W).symm.trans hg)
      ((Category.assoc (prismEndpoint 0 A) r W').symm.trans hg') η =
      relativeExtensionFiberEndpoint_witnessIso p β i hi v hv
        (prismEndpoint 0 A ≫ r) z hz W W' hW hW' hWi hWi' g g' hg hg' := by
  unfold relativePrismInitialEndpointIso
  exact eq_of_heq ((vertexIsoOfEq_heq _ _ _).trans
    (relativeExtensionPrismRestriction_endpoint_heq_witness p β i hi v hv
      W W' hW hW' hWi hWi' r 0 z hz g g' hg hg'))

/-- 同じ全延長比較の辺制限の実終点像は、元の全図式の同じ指定終点比較。 -/
lemma relativeExtensionPrism_actual_eq_witness (z : B _⦋0⦌)
    (hz : (prismEndpoint 1 A ≫ r) ≫ β = SSet.const z)
    (g g' : A ⟶ vertexFiber p z)
    (hg : (prismEndpoint 1 A ≫ r) ≫ W = g ≫ vertexFiberι p z)
    (hg' : (prismEndpoint 1 A ≫ r) ≫ W' = g' ≫ vertexFiberι p z) :
    relativePrismActualEndpointIso p (r ≫ β) z
      ((Category.assoc (prismEndpoint 1 A) r β).symm.trans hz)
      (r ≫ W) (r ≫ W') (by rw [Category.assoc, hW]) (by rw [Category.assoc, hW']) g g'
      ((Category.assoc (prismEndpoint 1 A) r W).symm.trans hg)
      ((Category.assoc (prismEndpoint 1 A) r W').symm.trans hg') η =
      relativeExtensionFiberEndpoint_witnessIso p β i hi v hv
        (prismEndpoint 1 A ≫ r) z hz W W' hW hW' hWi hWi' g g' hg hg' := by
  unfold relativePrismActualEndpointIso
  exact eq_of_heq ((vertexIsoOfEq_heq _ _ _).trans
    (relativeExtensionPrismRestriction_endpoint_heq_witness p β i hi v hv
      W W' hW hW' hWi hWi' r 1 z hz g g' hg hg'))

end SerrePositivity.InfinityCategories.F2
