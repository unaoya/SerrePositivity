module
public import SerrePositivity.KST.SConstruction.FamilyCylinderTriangleComparison

/-! # 一点上の元の全比較円柱を同じ写像空間の辺にする
概要：標準零単体をパラメータとする実円柱を、元の両端頂点を持つ実辺として読む。
方針：元の零単体の唯一の頂点で評価し、円柱全体の射を回収する。
規約：辺の代表を選び直さず、元の全区間の実写像を保持する。
使われ方：BF 境界比較を coherent nerve の合成面の入力に移す。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 一点上の元の二円柱を結ぶ全区間を、同じ元の写像空間の実辺として読む。 -/
def pointFamilyHomotopyEdge {E : SSet.{u}} {a b : (Δ[0] : SSet.{u}) ⟶ E}
    (H : SSet.Homotopy a b) : E.Edge (SSet.yonedaEquiv a) (SSet.yonedaEquiv b) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge H (SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{u})))

/-- 同じ元の全区間は、唯一の零頂点をパラメータとする元の円柱の実射そのもの。 -/
lemma pointFamilyHomotopyEdge_map {E : SSet.{u}} {a b : (Δ[0] : SSet.{u}) ⟶ E}
    (H : SSet.Homotopy a b) :
    SSet.yonedaEquiv.symm (pointFamilyHomotopyEdge H).edge =
      lift (SSet.const (SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{u})))) (𝟙 (Δ[1] : SSet.{u})) ≫ H.h := by
  apply SSet.yonedaEquiv.injective
  rw [Equiv.apply_symm_apply]
  have hi : SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})) = _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.edge := by
    apply stdSimplex.ext
    intro i
    fin_cases i <;> rfl
  change H.h.app (Opposite.op ⦋1⦌)
      ((SSet.Truncated.Edge.id (X := (truncation 2).obj (Δ[0] : SSet.{u}))
        (SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{u})))).edge, _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.edge) =
    H.h.app (Opposite.op ⦋1⦌)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{u}))) 1,
        SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})))
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_one, hi]

end SerrePositivity.KST.SConstruction
