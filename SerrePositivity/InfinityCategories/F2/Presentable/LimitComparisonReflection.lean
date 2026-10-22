module

public import SerrePositivity.InfinityCategories.Stable.LimitConeFamilies
public import SerrePositivity.InfinityCategories.Stable.MappingSpacePositiveBoundary
public import SerrePositivity.InfinityCategories.Stable.FullSubcomplexEdgeLift

/-!
概要：元の普遍錐全体から図式への射影は充満忠実で、比較の元の辺を保持する。
方針：相対終対象の正次元境界充填と全部分辺の持ち上げを再利用する。
規約：全図式の極限存在は仮定しない。指定された二つの全錐を保持する。
使われ方：Ind 比較の始域変数での全 Hom 極限表示。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable

/-- 相対終対象全体の射影は、追加の fibration 仮定なしに充満忠実。 -/
lemma relativeTerminalProjection_isFullyFaithful {E B : SSet.{u}}
    [Quasicategory E] [Quasicategory B] (p : E ⟶ B) :
    IsFullyFaithful (relativeTerminalProjection p) := by
  have : Quasicategory (relativeTerminalVertices p : SSet.{u}) :=
    fullSubcomplexOnVertices_quasicategory _ _
  exact isFullyFaithful_of_boundary_succ (relativeTerminalProjection p)
    (relativeTerminalProjection_hasLiftingProperty_boundary p)

/-- 同じ元の普遍錐の全射を、普遍錐の全部分圏の頂点へ戻す。 -/
def limitComparisonVertex {K X : SSet.{u}} [Quasicategory X] {p : K ⟶ X}
    (c : JoinCone p) (hc : IsLimitCone c) :
    (relativeTerminalVertices (coneRestriction K X)) _⦋0⦌ :=
  ⟨functorVertex c.val, by
    intro α
    have hα : α = 𝟙 ⦋0⦌ := Subsingleton.elim _ _
    rw [hα, op_id, CategoryTheory.Functor.map_id_apply]
    exact terminalBoundaryLifting_coneRestriction_of_isLimitCone c hc⟩

/-- 元の普遍錐間の全ホモトピーを、同じ一単体を持つ全部分圏の辺へ持ち上げる。 -/
def limitComparisonEdge {K X : SSet.{u}} [Quasicategory X] {p q : K ⟶ X}
    (c : JoinCone p) (d : JoinCone q) (hc : IsLimitCone c) (hd : IsLimitCone d)
    (H : SSet.Homotopy c.val d.val) :
    SSet.Truncated.Edge (X := (truncation 2).obj
      (relativeTerminalVertices (coneRestriction K X) : SSet.{u}))
      (limitComparisonVertex c hc) (limitComparisonVertex d hd) :=
  Classical.choose (exists_fullSubcomplexEdgeLift (TerminalBoundaryLifting (coneRestriction K X))
    (limitComparisonVertex c hc) (limitComparisonVertex d hd) (functorEdgeOfSimplicialHomotopy H))

/-- 元の全部分辺の包含像は、元のホモトピーの同じ関手辺。 -/
lemma limitComparisonEdge_map {K X : SSet.{u}} [Quasicategory X] {p q : K ⟶ X}
    (c : JoinCone p) (d : JoinCone q) (hc : IsLimitCone c) (hd : IsLimitCone d)
    (H : SSet.Homotopy c.val d.val) :
    (limitComparisonEdge c d hc hd H).map
      ((truncation 2).map (relativeTerminalVertices (coneRestriction K X)).ι) =
        functorEdgeOfSimplicialHomotopy H :=
  Classical.choose_spec (exists_fullSubcomplexEdgeLift
    (TerminalBoundaryLifting (coneRestriction K X))
    (limitComparisonVertex c hc) (limitComparisonVertex d hd) (functorEdgeOfSimplicialHomotopy H))

end SerrePositivity.InfinityCategories.F2.Presentable
