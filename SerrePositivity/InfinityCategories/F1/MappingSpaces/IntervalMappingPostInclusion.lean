module

public import SerrePositivity.InfinityCategories.F1.MappingSpaces.IntervalMappingPostIso

/-!
概要：端点を正規化した区間 Hom の後合成は、包含後に元の内部 Hom の後合成となる。
方針：同じ族を展開し、uncurry の自然性と単射性を使う。
規約：元の区間 Hom の包含を使う。
使われ方：相対内部 Hom の持ち上げを、同じ固定端点の区間 Hom へ戻す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 同じ後合成の族を含めると、元の全区間関手空間の後合成となる。 -/
lemma intervalMappingPostOfEq_ι {T X Y : SSet.{u}} (p : X ⟶ Y)
    (x y : X _⦋0⦌) {x' y' : Y _⦋0⦌} (hx : p.app _ x = x') (hy : p.app _ y = y')
    (s : T ⟶ intervalMappingSpace x y) :
    (s ≫ intervalMappingPostOfEq p x y hx hy) ≫
        vertexFiberι ((pre (boundary 1).ι).app Y)
          (functorVertex (intervalMappingBoundary x' y')) =
      (s ≫ vertexFiberι ((pre (boundary 1).ι).app X)
        (functorVertex (intervalMappingBoundary x y))) ≫ (ihom (Δ[1] : SSet.{u})).map p := by
  apply uncurry_injective
  change intervalMappingUncurry (s ≫ intervalMappingPostOfEq p x y hx hy) = _
  rw [intervalMappingPostOfEq_uncurry, uncurry_natural_right]
  rfl

end SerrePositivity.InfinityCategories
