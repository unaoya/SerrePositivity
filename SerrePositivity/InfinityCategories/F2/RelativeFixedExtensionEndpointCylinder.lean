module

public import SerrePositivity.InfinityCategories.F2.RelativeFixedExtensionCurry
public import SerrePositivity.InfinityCategories.F2.RelativeExtensionFiberEndpointEvaluation

/-!
概要：元の実固定円柱の fiber 終点像は同じ円柱の実際の制限。
方針：同じ終点評価を uncurry し、元の固定円柱を回収する。
規約：全係数と指定終点を保持する。
使われ方：既存の指定比較の終点像を元の精密化の作用へ同定する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 同じ延長空間の実族の終点像は元の実円柱を同じ終点へ制限した射。 -/
lemma relativeFixedExtensionCurry_endpoint_uncurry
    {D A T C E B : SSet.{u}} (p : E ⟶ B) (b : A ⟶ B)
    (i : D ⟶ A) (v : D ⟶ E) (hv : v ≫ p = i ≫ b)
    (H : A ⊗ T ⟶ E) (hB : H ≫ p = fst A T ≫ b)
    (hV : (i ▷ T) ≫ H = fst D T ≫ v)
    (j : C ⟶ A) (y : B _⦋0⦌) (hy : j ≫ b = SSet.const y) :
    uncurry (relativeFixedExtensionCurry p b i v hv H hB hV ≫
      relativeExtensionFiberEndpoint p b i v hv j y hy) ≫ vertexFiberι p y = (j ▷ T) ≫ H := by
  rw [uncurry_natural_left, Category.assoc, relativeExtensionFiberEndpoint_uncurry_ι,
    ← relativeFunctorUncurry_parameter, ← Category.assoc, relativeFunctorUncurry_pre,
    relativeFixedExtensionCurry_uncurry]

end SerrePositivity.InfinityCategories.F2
