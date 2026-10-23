module
public import SerrePositivity.InfinityCategories.F1B.VertexFiberBaseChange
public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.LeftUnstraighteningFiberIso

/-! # 同じ第一射影を保つ既存の二つの実底変換 fiber 同型の順方向射を照合する -/

@[expose] public section
noncomputable section
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Fibration

/-- 既存の二つの底変換 fiber 同型は、同じ順方向射を指定している。 -/
theorem cofinalVertexFiberBaseChangeIso_hom_eq {E B D : SSet.{u}}
    (p : E ⟶ B) (k : D ⟶ B) (d : D _⦋0⦌) :
    (cofinalVertexFiberBaseChangeIso p k d).hom = (vertexFiberPullbackIso p k d).hom := rfl

end SerrePositivity.KST.Fibration
