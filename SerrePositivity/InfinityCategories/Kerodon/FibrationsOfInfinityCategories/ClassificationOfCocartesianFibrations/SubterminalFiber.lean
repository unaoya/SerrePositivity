module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.FunctorFiber

/-!
概要：各次数で高々一点の底における fiber の包含の同型性。
方針：底での二つの単体の等式を一意性から与え、fiber への逆の持ち上げを作る。
規約：底に指定する頂点 b の存在を仮定する。fibration 性は不要。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、一点を底とする分類の写像空間の比較。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 概要：各次数で高々一点の底上の fiber は、元の全空間と同型。
方針：包含を順方向とし、恒等射を fiber に持ち上げて逆にする。
規約：各次数の Subsingleton と指定した底の頂点を用いる。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、一点上の fiber と全空間の厳密な比較。 -/
def vertexFiberSubterminalBaseIso {E B : SSet.{u}}
    [∀ n : SimplexCategoryᵒᵖ, Subsingleton (B.obj n)] (p : E ⟶ B) (b : B _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p b ≅ E where
  hom := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p b
  inv := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift p b (𝟙 E) (by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro x
    exact Subsingleton.elim _ _)
  hom_inv_id := by
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_hom_ext p b
    simp only [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift_ι, Category.comp_id, Category.id_comp]
  inv_hom_id := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift_ι _ _ _ _

/-- 概要：各次数で高々一点の底を持つ内部 Hom は各次数で高々一点。
方針：内部 Hom の単体を自然変換の各入力で比較し、底の単体の一意性を使う。
規約：始域 A は任意。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、一点上の相対 Hom の固定条件を消去する。 -/
instance ihom_subsingleton_of_subterminal {A B : SSet.{u}}
    [∀ n : SimplexCategoryᵒᵖ, Subsingleton (B.obj n)] (n : SimplexCategoryᵒᵖ) :
    Subsingleton (((ihom A).obj B).obj n) where
  allEq f g := by
    apply CategoryTheory.Functor.functorHom_ext
    intro d α
    apply ConcreteCategory.hom_ext
    intro x
    exact Subsingleton.elim _ _

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
