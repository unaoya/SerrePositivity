module

public import SerrePositivity.InfinityCategories.F1.IntervalHomFamilyProjection
public import SerrePositivity.InfinityCategories.F1.IntervalHomPathSpan
public import SerrePositivity.InfinityCategories.Core.EquivalencePathMap

/-!
概要：同じ可逆 path の Hom の後合成は、指定した元の端点の評価と厳密に可換。
方針：全区間族を展開し、元の可逆 path の後合成と端点評価の自然性を使う。
規約：端点の正規化と元の path の族を保持する。
使われ方：既存の元の Hom 輸送の底の制限に関する自然性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 同じ path の Hom の後合成と、元の指定端点への評価は厳密に可換。 -/
lemma intervalHomPathMap_endpoint
    {A X Y : SSet.{u}} (P : A ⟶ equivalencePath X) (f : X ⟶ Y)
    (Q : A ⟶ equivalencePath Y) (h : P ≫ equivalencePathMap f = Q)
    (a b : A _⦋0⦌) (i : Fin 2) {x y : X _⦋0⦌} {x' y' : Y _⦋0⦌}
    (hx : (P ≫ equivalencePathEndpoint X i).app _ a = x)
    (hy : (P ≫ equivalencePathEndpoint X i).app _ b = y)
    (hx' : (Q ≫ equivalencePathEndpoint Y i).app _ a = x')
    (hy' : (Q ≫ equivalencePathEndpoint Y i).app _ b = y')
    (hf : f.app _ x = x') (hg : f.app _ y = y') :
    intervalHomPathEndpoint P i a b hx hy ≫ intervalMappingPostOfEq f x y hf hg =
      intervalHomFamilyProjection P (equivalencePathMap f) Q h a b ≫
        intervalHomPathEndpoint Q i a b hx' hy' := by
  apply intervalMappingUncurry_injective
  rw [intervalMappingPostOfEq_uncurry, intervalHomPathEndpoint_uncurry,
    intervalHomFamilyProjection, intervalMappingPostOfEq_universal_uncurry,
    intervalHomPathEndpoint, intervalMappingPostOfEq_universal_uncurry,
    Category.assoc, Category.assoc, equivalencePathMap_endpoint]

end SerrePositivity.InfinityCategories
