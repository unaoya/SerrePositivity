module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.PrismContraction
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic

/-!
概要：prism の指定係数頂点における垂直一単体。
方針：scaffold と無関係な宣言を元の本文のまま分離する。
規約：公開名・型・評価式は原本を保持する。
使われ方：inner anodyne な prism 延長と相対 join の比較。

対応節は Kerodon 5.2（Tag 019A）。
-/
@[expose] public section
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport

/-- 概要：prism の指定係数頂点を固定した垂直一単体。
方針：標準区間の恒等一単体と係数頂点の定値一単体を組にして評価する。
規約：辺の向きは時刻零から一。
使われ方：Kerodon Theorem 5.2.4.1（Tag 024N）、各係数頂点に対する cocartesian 条件。 -/
def prismVerticalSimplex {K E : SSet.{u}} (H : (Δ[1] : SSet.{u}) ⊗ K ⟶ E)
    (x : K _⦋0⦌) : E _⦋1⦌ :=
  H.app (Opposite.op ⦋1⦌)
    (stdSimplex.objEquiv.symm (𝟙 ⦋1⦌), _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant x 1)


end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport
