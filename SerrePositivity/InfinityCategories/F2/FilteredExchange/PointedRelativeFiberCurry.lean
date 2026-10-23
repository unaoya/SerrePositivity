module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentFiberPointedSourceIso
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.RelativeFiberRestriction

/-!
概要：元の値に定値な pointed 全族を、元の小さい fiber 間の関手族へ厳密に移す。
方針：定値の底の fiber Hom に、元の fiber 同型の逆を後合成する。
規約：元の頂点と全パラメータを保持。使われ方：旧 prism 出力と新しい端点評価の照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {B : SSet.{u}} {A : SSet.{u + 1}}
  (J : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}) (b : B _⦋0⦌)
  (a : A ⟶ SpaceInfinity.{u}) (ha : a = SSet.const (J.app (Opposite.op ⦋0⦌) (ULift.up b)))

/-- 同じ定値の底の pointed 全族を、元の小さい fiber への関手族へ写す。 -/
def pointedRelativeFiberCurry : relativeFunctorSpace pointedSpaceProjection a ⟶
    (ihom A).obj (coherentNativeTriangleFiberParameters J b) :=
  relativeFunctorBaseFiberHom pointedSpaceProjection a (J.app _ (ULift.up b)) ha ≫
    (ihom A).map (coherentFiberPointedSourceIso J b).inv

/-- 元の pointed 始点族へ含めると、同じ全相対族を厳密に回収する。 -/
lemma pointedRelativeFiberCurry_pointed :
    uncurry (pointedRelativeFiberCurry J b a ha) ≫ coherentCospanFiberPointedSource J b =
      relativeFunctorUncurry (𝟙 (relativeFunctorSpace pointedSpaceProjection a)) := by
  rw [pointedRelativeFiberCurry, uncurry_natural_right, Category.assoc,
    ← coherentFiberPointedSourceIso_hom_ι J b, Iso.inv_hom_id_assoc]
  exact relativeFunctorBaseFiberHom_uncurry_ι _ _ _ _

end SerrePositivity.InfinityCategories.F2
