module

public import SerrePositivity.KST.LocalizingInvariants.ZeroCospanRestriction
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.VertexTransport.FullSubcomplexEdgeLift
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.MappingSpaces.HomotopyPrecomposition

/-!
概要：零第二枝を持つ cospan 比較の類は、第一枝への全関手としての制限で決まる。
方針：比較辺を零枝の全部分圏へ持ち上げ、第一枝射影の充満忠実性で戻す。
規約：頂点成分の一致には弱めない。使われ方：指定 prism の fiber 射の同定。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants.ZeroCospan

variable {X : SSet.{u}}

def vertex (F : (horn 2 2 : SSet.{u}) ⟶ X) (hF : zeroSecond X (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F)) :
    (diagrams X) _⦋0⦌ :=
  ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F, by
    intro α
    have hα : α = 𝟙 ⦋0⦌ := Subsingleton.elim _ _
    rw [hα, op_id, CategoryTheory.Functor.map_id_apply]
    exact hF⟩

def homotopyEdge (F G : (horn 2 2 : SSet.{u}) ⟶ X)
    (hF : zeroSecond X (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F)) (hG : zeroSecond X (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex G))
    (H : SSet.Homotopy F G) :
    Truncated.Edge (X := (truncation 2).obj (diagrams X)) (vertex F hF) (vertex G hG) :=
  Classical.choose (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.exists_fullSubcomplexEdgeLift (zeroSecond X)
    (vertex F hF) (vertex G hG) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H))

lemma homotopyEdge_map (F G : (horn 2 2 : SSet.{u}) ⟶ X)
    (hF : zeroSecond X (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F)) (hG : zeroSecond X (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex G))
    (H : SSet.Homotopy F G) :
    (homotopyEdge F G hF hG H).map ((truncation 2).map (inclusion X)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H :=
  Classical.choose_spec (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.exists_fullSubcomplexEdgeLift (zeroSecond X)
    (vertex F hF) (vertex G hG) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H))

lemma homotopy_homMk_eq [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.HasZeroVertex X]
    (F G : (horn 2 2 : SSet.{u}) ⟶ X)
    (hF : zeroSecond X (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F)) (hG : zeroSecond X (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex G))
    (H J : SSet.Homotopy F G)
    (h : Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
        (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.stableHomotopyPrecomp horn₂₂.ι₀₂ H)) =
      Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
        (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.stableHomotopyPrecomp horn₂₂.ι₀₂ J))) :
    Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H) =
      Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy J) := by
  let i := inclusion X
  let a := Truncated.HomotopyCategory.homMk (homotopyEdge F G hF hG H)
  let b := Truncated.HomotopyCategory.homMk (homotopyEdge F G hF hG J)
  have ha : (hoFunctor.map i).toFunctor.map a =
      Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H) :=
    congrArg Truncated.HomotopyCategory.homMk (homotopyEdge_map F G hF hG H)
  have hb : (hoFunctor.map i).toFunctor.map b =
      Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy J) :=
    congrArg Truncated.HomotopyCategory.homMk (homotopyEdge_map F G hF hG J)
  have hab : a = b := by
    apply (first_isFullyFaithful X).toHoFullyFaithful.map_injective
    change (hoFunctor.map ((pre horn₂₂.ι₀₂).app X)).toFunctor.map
      ((hoFunctor.map i).toFunctor.map a) =
        (hoFunctor.map ((pre horn₂₂.ι₀₂).app X)).toFunctor.map
          ((hoFunctor.map i).toFunctor.map b)
    rw [ha, hb, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.homMk_functorEdge_precomp, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.homMk_functorEdge_precomp]
    exact h
  exact ha.symm.trans ((congrArg (fun f ↦ (hoFunctor.map i).toFunctor.map f) hab).trans hb)

end SerrePositivity.KST.LocalizingInvariants.ZeroCospan
