module

public import SerrePositivity.InfinityCategories.F1.CartesianEdge
public import SerrePositivity.InfinityCategories.Core.PrismContraction
public import SerrePositivity.InfinityCategories.PinchedHom.Basic

/-!
概要：prism の垂直辺を指定頂点で評価する。
方針：区間の恒等一単体と係数頂点の定値単体を代入する。
規約：有限 scaffold や straightening には依存しない。
使われ方：写像円柱の比較と相対 join の輸送。
-/
@[expose] public section
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.KanSection
/-- 概要：prism の指定係数頂点を固定した垂直一単体。
方針：標準区間の恒等一単体と係数頂点の定値一単体を組にして評価する。
規約：辺の向きは時刻零から一。
使われ方：Kerodon Theorem 5.2.4.1、各係数頂点に対する cocartesian 条件。 -/
def prismVerticalSimplex {K E : SSet.{u}} (H : (Δ[1] : SSet.{u}) ⊗ K ⟶ E)
    (x : K _⦋0⦌) : E _⦋1⦌ :=
  H.app (Opposite.op ⦋1⦌)
    (stdSimplex.objEquiv.symm (𝟙 ⦋1⦌), PinchedHom.constant x 1)

end SerrePositivity.InfinityCategories.KanSection
