module

public import SerrePositivity.KST.LocalizingInvariants.FiberConeFullyFaithful
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.FullSubcomplexEdgeLift
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanHomotopyEquivalence

/-!
概要：図式の比較を固定した普遍錐間のホモトピーの類の一意性。
方針：元の関手辺を普遍錐の全部分圏へ持ち上げ、図式射影の忠実性を適用する。
規約：同じ両端と全図式の比較の類を保持。使われ方：元の fiber 頂点の射の同定。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants.FiberCone

def vertex {K X : SSet.{u}} [Quasicategory X] {p : K ⟶ X}
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone c) : (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.limitCones K X) _⦋0⦌ :=
  ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex c.val, by
    intro α
    have hα : α = 𝟙 ⦋0⦌ := Subsingleton.elim _ _
    rw [hα, op_id, CategoryTheory.Functor.map_id_apply]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.terminalBoundaryLifting_coneRestriction_of_isLimitCone c hc⟩

def homotopyEdge {K X : SSet.{u}} [Quasicategory X] {p q : K ⟶ X}
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p) (d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone q) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone c) (hd : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone d)
    (H : SSet.Homotopy c.val d.val) :
    SSet.Truncated.Edge (X := (truncation 2).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.limitCones K X))
      (vertex c hc) (vertex d hd) :=
  Classical.choose (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.exists_fullSubcomplexEdgeLift (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TerminalBoundaryLifting (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coneRestriction K X))
    (vertex c hc) (vertex d hd) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H))

/-- 概要：普遍錐全体へ持ち上げた辺を含めると元のホモトピーの関手辺に戻る。
方針：辺の持ち上げの付随条件。
規約：端点も含む辺の等号。使われ方：ホモトピー圏の射の照合。 -/
lemma homotopyEdge_map {K X : SSet.{u}} [Quasicategory X] {p q : K ⟶ X}
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p) (d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone q) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone c) (hd : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone d)
    (H : SSet.Homotopy c.val d.val) :
    (homotopyEdge c d hc hd H).map
      ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.relativeTerminalVertices (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coneRestriction K X)).ι) =
        _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H :=
  Classical.choose_spec (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.exists_fullSubcomplexEdgeLift
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TerminalBoundaryLifting (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coneRestriction K X))
    (vertex c hc) (vertex d hd) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H))

/-- 概要：普遍錐間の比較ホモトピーは、図式へ制限した h の類が等しければ同じ類を与える。
方針：普遍錐の全部分圏へ持ち上げ、射影の忠実性を適用してから包含で戻す。
規約：図式の比較の類だけを固定する。使われ方：接続射の比較。 -/
lemma homotopy_homMk_eq {K X : SSet.{u}} [Quasicategory X] {p q : K ⟶ X}
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p) (d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone q) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone c) (hd : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone d)
    (H J : SSet.Homotopy c.val d.val)
    (h : (hoFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coneRestriction K X)).toFunctor.map
      (SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H)) =
      (hoFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coneRestriction K X)).toFunctor.map
        (SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy J))) :
    SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H) =
      SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy J) := by
  let i := (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.relativeTerminalVertices (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coneRestriction K X)).ι
  let u := SSet.Truncated.HomotopyCategory.homMk (homotopyEdge c d hc hd H)
  let v := SSet.Truncated.HomotopyCategory.homMk (homotopyEdge c d hc hd J)
  have hu : (hoFunctor.map i).toFunctor.map u =
      SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H) :=
    congrArg SSet.Truncated.HomotopyCategory.homMk (homotopyEdge_map c d hc hd H)
  have hv : (hoFunctor.map i).toFunctor.map v =
      SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy J) :=
    congrArg SSet.Truncated.HomotopyCategory.homMk (homotopyEdge_map c d hc hd J)
  have huv : u = v := by
    apply projection_map_injective
    change (hoFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coneRestriction K X)).toFunctor.map
      ((hoFunctor.map i).toFunctor.map u) =
        (hoFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coneRestriction K X)).toFunctor.map ((hoFunctor.map i).toFunctor.map v)
    rw [hu, hv]
    exact h
  have he := congrArg (fun f ↦ (hoFunctor.map i).toFunctor.map f) huv
  exact hu.symm.trans (he.trans hv)


end SerrePositivity.KST.LocalizingInvariants.FiberCone
