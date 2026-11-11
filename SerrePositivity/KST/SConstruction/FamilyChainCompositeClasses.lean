module
public import SerrePositivity.KST.SConstruction.FamilyChainCompositeData

/-! # 実合成木と元の全補正列の合成式
概要：全二単体を保持した合成木が、元の有限列の同じ合成を表すことを証明する。
方針：各元の合成三角形の式を、列の全区間について帰納的に合成する。
規約：この等式から元の raw 族の等号を推論せず、実三角形の比較構成に使う。
使われ方：同じ有限列を合成した二つの実円柱の端点固定比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 元の全実区間の、内部 Hom のホモトピー圏での順序を保つ実合成。 -/
def familyChainCompositeClass {U E : SSet.{u}} {f g : U ⟶ E} (c : FamilyHomotopyChain f g) :
    _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom f g :=
  match c with
  | .nil f => 𝟙 _
  | .cons a tail => SSet.Truncated.HomotopyCategory.homMk
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy a) ≫ familyChainCompositeClass tail

/-- 元の全三角形の合成式により、合成円柱は元の全区間の同じ順序の合成を表す。 -/
lemma familyChainCompositionWitness_class {U E : SSet.{u}} {f g : U ⟶ E}
    {c : FamilyHomotopyChain f g} {H : SSet.Homotopy f g}
    (w : FamilyChainCompositionWitness c H) :
    SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H) =
      familyChainCompositeClass c := by
  induction w with
  | nil f => exact _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyRefl_hom f
  | cons a tail tailWitness triangle ih =>
      exact (SSet.HomotopyCategory.homMk_comp_homMk triangle).symm.trans
        (congrArg (fun h => SSet.Truncated.HomotopyCategory.homMk
          (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy a) ≫ h) ih)

/-- 同じ全区間から得た任意の二つの実合成木は、端点を保つ同じ辺の合成を表す。 -/
lemma familyChainCompositionWitness_class_eq {U E : SSet.{u}} {f g : U ⟶ E}
    {c : FamilyHomotopyChain f g} {H K : SSet.Homotopy f g}
    (w : FamilyChainCompositionWitness c H) (v : FamilyChainCompositionWitness c K) :
    SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H) =
      SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy K) :=
  (familyChainCompositionWitness_class w).trans (familyChainCompositionWitness_class v).symm

/-- 同じ全区間の二つの合成円柱を、元の全辺を三面に持つ実三角形で比較する。 -/
def familyChainCompositionComparisonTriangle {U E : SSet.{u}} [KanComplex E]
    {f g : U ⟶ E} {c : FamilyHomotopyChain f g} {H K : SSet.Homotopy f g}
    (w : FamilyChainCompositionWitness c H) (v : FamilyChainCompositionWitness c K) :
    SSet.Edge.CompStruct
      (SSet.Edge.ofTruncated (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H))
      (SSet.Edge.id (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex g))
      (SSet.Edge.ofTruncated (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy K)) := by
  have h : SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H) ≫
      SSet.Truncated.HomotopyCategory.homMk
        (SSet.Edge.id (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex g)).toTruncated =
      SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy K) := by
    change SSet.HomotopyCategory.homMk
      (SSet.Edge.ofTruncated (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H)) ≫
        SSet.HomotopyCategory.homMk (SSet.Edge.id (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex g)) = _
    rw [SSet.HomotopyCategory.homMk_id, Category.comp_id]
    exact familyChainCompositionWitness_class_eq w v
  exact SSet.Edge.CompStruct.ofTruncated (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.compStruct_nonempty_of_homMk_fac h).some

end SerrePositivity.KST.SConstruction
