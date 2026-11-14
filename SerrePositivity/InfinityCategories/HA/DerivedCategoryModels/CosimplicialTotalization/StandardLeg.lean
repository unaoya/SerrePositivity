module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.StandardZeroLeg

/-!
概要：元の積Totから各余単体次数への、第0頂点を選ぶ同じ標準脚を固定する。
方針：指定零行射影を第0頂点の定数射で後合成し、両方の自然性を使う。
規約：IS-W2 C01の型に現れる既存標準脚。各次数で別の頂点を選ばない。
使われ方：HA 1.2.4、native脚と全図式射の最終照合。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization
open CategoryTheory
open SerrePositivity.DifferentialGraded
open scoped Simplicial
variable (A : Type u) [CommRing A]

/-- 指定零行射影から第0頂点を通って各余単体次数へ向かう標準脚。 -/
def standardLeg (X : CosimplicialObject (Complex A)) (n : SimplexCategory) :
    (productTotalFunctor A).obj X ⟶ X.obj n :=
  standardZeroLeg A X ≫ X.map (SimplexCategory.const ⦋0⦌ n 0)

/-- 同じ標準脚は、元の積Tot関手の全図式射に自然。 -/
theorem standardLeg_naturality {X Y : CosimplicialObject (Complex A)}
    (f : X ⟶ Y) (n : SimplexCategory) :
    (productTotalFunctor A).map f ≫ standardLeg A Y n =
      standardLeg A X n ≫ f.app n := by
  dsimp only [standardLeg]
  rw [← Category.assoc, standardZeroLeg_naturality, Category.assoc, ← f.naturality,
    ← Category.assoc]

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization
