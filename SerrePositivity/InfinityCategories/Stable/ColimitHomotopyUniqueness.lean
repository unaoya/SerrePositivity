module
public import SerrePositivity.InfinityCategories.Stable.FullSubcomplexEdgeLift
public import SerrePositivity.InfinityCategories.Stable.ColimitCoconeEdges
public import SerrePositivity.InfinityCategories.Stable.ColimitFullyFaithful
public import SerrePositivity.InfinityCategories.Core.KanHomotopyEquivalence

/-! # 普遍余錐間の比較ホモトピーの一意性

概要：普遍余錐間の比較ホモトピーの h の類は、図式へ制限した類で決まる。
方針：ホモトピーの辺を普遍余錐の全部分圏へ持ち上げ、射影の忠実性を使う。
規約：実際の辺の選択を固定せずに比較する。
使われ方：S4 の cofiber 接続射の選択独立性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：指定普遍余錐間のホモトピーを普遍余錐全体の辺として表す。
方針：全部分単体集合への辺の持ち上げを使う。
規約：元の関手辺の一次単体を変えない。使われ方：射影の忠実性による比較。 -/
def colimitCoconeHomotopyEdge {K X : SSet.{u}} [Quasicategory X] {p q : K ⟶ X}
    (c : JoinCocone p) (d : JoinCocone q) (hc : IsColimitCone c) (hd : IsColimitCone d)
    (H : SSet.Homotopy c.val d.val) :
    SSet.Truncated.Edge (X := (truncation 2).obj (colimitCocones K X))
      (colimitCoconeVertex c hc) (colimitCoconeVertex d hd) :=
  Classical.choose (exists_fullSubcomplexEdgeLift (InitialBoundaryLifting (coconeRestriction K X))
    (colimitCoconeVertex c hc) (colimitCoconeVertex d hd) (functorEdgeOfSimplicialHomotopy H))

/-- 概要：普遍余錐全体へ持ち上げた辺を含めると元のホモトピーの関手辺に戻る。
方針：辺の持ち上げの付随条件。
規約：端点も含む辺の等号。使われ方：ホモトピー圏の射の照合。 -/
lemma colimitCoconeHomotopyEdge_map {K X : SSet.{u}} [Quasicategory X] {p q : K ⟶ X}
    (c : JoinCocone p) (d : JoinCocone q) (hc : IsColimitCone c) (hd : IsColimitCone d)
    (H : SSet.Homotopy c.val d.val) :
    (colimitCoconeHomotopyEdge c d hc hd H).map
      ((truncation 2).map (relativeInitialVertices (coconeRestriction K X)).ι) =
        functorEdgeOfSimplicialHomotopy H :=
  Classical.choose_spec (exists_fullSubcomplexEdgeLift
    (InitialBoundaryLifting (coconeRestriction K X))
    (colimitCoconeVertex c hc) (colimitCoconeVertex d hd) (functorEdgeOfSimplicialHomotopy H))

/-- 概要：普遍余錐間の比較ホモトピーは、図式へ制限した h の類が等しければ同じ類を与える。
方針：普遍余錐の全部分圏へ持ち上げ、射影の忠実性を適用してから包含で戻す。
規約：図式の比較の類だけを固定する。使われ方：接続射の比較。 -/
lemma colimitCoconeHomotopy_homMk_eq {K X : SSet.{u}} [Quasicategory X] {p q : K ⟶ X}
    (c : JoinCocone p) (d : JoinCocone q) (hc : IsColimitCone c) (hd : IsColimitCone d)
    (H J : SSet.Homotopy c.val d.val)
    (h : (hoFunctor.map (coconeRestriction K X)).toFunctor.map
      (SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy H)) =
      (hoFunctor.map (coconeRestriction K X)).toFunctor.map
        (SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy J))) :
    SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy H) =
      SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy J) := by
  let i := (relativeInitialVertices (coconeRestriction K X)).ι
  let u := SSet.Truncated.HomotopyCategory.homMk (colimitCoconeHomotopyEdge c d hc hd H)
  let v := SSet.Truncated.HomotopyCategory.homMk (colimitCoconeHomotopyEdge c d hc hd J)
  have hu : (hoFunctor.map i).toFunctor.map u =
      SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy H) :=
    congrArg SSet.Truncated.HomotopyCategory.homMk (colimitCoconeHomotopyEdge_map c d hc hd H)
  have hv : (hoFunctor.map i).toFunctor.map v =
      SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy J) :=
    congrArg SSet.Truncated.HomotopyCategory.homMk (colimitCoconeHomotopyEdge_map c d hc hd J)
  have huv : u = v := by
    apply colimitCoconeProjection_ho_map_injective
    change (hoFunctor.map (coconeRestriction K X)).toFunctor.map
      ((hoFunctor.map i).toFunctor.map u) =
        (hoFunctor.map (coconeRestriction K X)).toFunctor.map ((hoFunctor.map i).toFunctor.map v)
    rw [hu, hv]
    exact h
  have he := congrArg (fun f ↦ (hoFunctor.map i).toFunctor.map f) huv
  exact hu.symm.trans (he.trans hv)

end SerrePositivity.InfinityCategories
