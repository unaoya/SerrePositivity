module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.RelativeExtensionFiberEndpointEvaluation
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.UniversalScaffoldEvaluation

/-!
概要：指定 fiber 終点の係数の前合成は、元の全延長評価の同じ前合成になる。
方針：fiber 包含後の全評価と内部 Hom の前合成を計算する。
規約：元の初期値と全延長空間を保持。使われ方：元の一点比較の全係数への移送。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 同じ指定終点での係数制限は、元の全 fiber 評価の前合成そのもの。 -/
lemma relativeExtensionFiberEndpoint_precomp {A D C C' E B : SSet.{u}}
    (p : E ⟶ B) (a : A ⟶ B) (i : D ⟶ A) (v : D ⟶ E) (hv : v ≫ p = i ≫ a)
    (j : C ⟶ A) (b : B _⦋0⦌) (hj : j ≫ a = SSet.const b) (s : C' ⟶ C) :
    relativeExtensionFiberEndpoint p a i v hv (s ≫ j) b
      (by rw [Category.assoc, hj, SSet.comp_const]) =
    relativeExtensionFiberEndpoint p a i v hv j b hj ≫ (pre s).app (vertexFiber p b) := by
  apply uncurry_injective
  apply vertexFiber_hom_ext p b
  rw [uncurry_pre_app, Category.assoc, relativeExtensionFiberEndpoint_uncurry_ι,
    relativeExtensionFiberEndpoint_uncurry_ι, relativeFunctorUncurry_pre,
    relativeFunctorUncurry_pre, ← Category.assoc, ← comp_whiskerRight]

end SerrePositivity.InfinityCategories.F2
