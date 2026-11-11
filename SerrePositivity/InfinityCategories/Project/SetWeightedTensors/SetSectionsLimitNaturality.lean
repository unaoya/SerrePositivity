module

public import SerrePositivity.InfinityCategories.Project.SetWeightedTensors.SetSectionsNaturality
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.NormalizedConeRestrictionComparison
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.FixedApexLimitCriterion
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.KanInvertible

/-!
概要：切断制限の自然性を、固定頂点の錐の族と極限の一意性へ帰着する補助。
方針：制限の共通模型を固定し、極限錐の比較同値で全パラメータの同型を反映する。
規約：G8 の四角形そのものはまだ主張しない。頂点ごとの一致には弱めない。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.SetWeightedTensors

namespace SetWeight

/-- 極限頂点の標準同型の順射は、錐の圏で指定した任意の普遍辺の射影の類。
頂点の同型だけを比較せず、錐全体の終対象性を使う。 -/
lemma limitVertexIso_hom_eq_coneEdge
    {K E : SSet.{u}} [Quasicategory E] {p : K ⟶ E}
    (c d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone c) (hd : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone d)
    (e : SSet.Edge (X := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver p) c d) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.limitVertexIso c d hc hd).hom =
      Truncated.HomotopyCategory.homMk (e.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection p)).toTruncated := by
  have h : (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.limitConeIso c d hc hd).hom =
      Truncated.HomotopyCategory.homMk e.toTruncated :=
    (show _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex (X := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver p) d from hd).isTerminalHo.hom_ext _ _
  change (hoFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection p)).toFunctor.map
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.limitConeIso c d hc hd).hom = _
  rw [h]
  rfl

/-- 極限への写像の族を、両端固定の錐の族へ写す比較。 -/
def limitConeEndpointComparison {K E : SSet.{u}} [Quasicategory E]
    {p : K ⟶ E} (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p) (x : E _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom x c.vertex ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fixedEndpointConeSpace p x :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.fixedApexConeHomComparison c x ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fixedApexEndpointConeSpaceIso p x).hom

/-- 指定錐の極限性により、錐の族への比較は全写像空間の同値となる。 -/
lemma limitConeEndpointComparison_isQCatEquivalence
    {K E : SSet.{u}} [Quasicategory E] {p : K ⟶ E}
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone c) (x : E _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (limitConeEndpointComparison c x) :=
  ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.isLimitCone_iff_fixedApexConeHomComparison_homotopyEquivalence c).mp hc x
    ).isQCatEquivalence.comp
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fixedApexEndpointConeSpaceIso p x)).isQCatEquivalence

/-- 錐の族として同型な二つの写像の族は、極限への写像の族として同型。
パラメータ A 全体を保持し、各頂点での射の一意性だけには帰着しない。 -/
def limitConeMapIsoOfConeFamilyIso {A K E : SSet.{u}} [Quasicategory E]
    {p : K ⟶ E} (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone c) (x : E _⦋0⦌)
    (a b : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom x c.vertex)
    (h : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (a ≫ limitConeEndpointComparison c x)
      (b ≫ limitConeEndpointComparison c x)) : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso a b := by
  let e := (limitConeEndpointComparison_isQCatEquivalence c hc x).choose
  have he : e.hom = limitConeEndpointComparison c x := rfl
  have ha : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (a ≫ limitConeEndpointComparison c x ≫ e.inv) a := by
    simpa only [Category.assoc, Category.comp_id, he] using e.homInvIso.precomp a
  have hb : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (b ≫ limitConeEndpointComparison c x ≫ e.inv) b := by
    simpa only [Category.assoc, Category.comp_id, he] using e.homInvIso.precomp b
  have hab : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (a ≫ limitConeEndpointComparison c x ≫ e.inv)
      (b ≫ limitConeEndpointComparison c x ≫ e.inv) := by
    simpa only [Category.assoc] using h.postcomp e.inv
  exact ha.symm ≪≫ hab ≪≫ hb

/-- 錐の族の同型から、空間のホモトピー圏での写像の等式を得る。 -/
lemma limitConeMap_homMk_eq_of_coneFamilyIso
    {A K E : SSet.{u}} [KanComplex A] [Quasicategory E]
    {p : K ⟶ E} (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone c) (x : E _⦋0⦌)
    (a b : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom x c.vertex)
    (h : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (a ≫ limitConeEndpointComparison c x)
      (b ≫ limitConeEndpointComparison c x)) :
    Truncated.HomotopyCategory.homMk
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (C := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u})
        (X := ⟨A, inferInstance⟩) (Y := ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom x c.vertex, inferInstance⟩) a).toTruncated =
    Truncated.HomotopyCategory.homMk
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (C := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u})
        (X := ⟨A, inferInstance⟩) (Y := ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom x c.vertex, inferInstance⟩) b).toTruncated := by
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentKanEdge_homMk_eq_of_functorIso
    (K := ⟨A, inferInstance⟩) (L := ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom x c.vertex, inferInstance⟩)
    (limitConeMapIsoOfConeFamilyIso c hc x a b h)

variable {I : Type u} [SmallCategory I] {X Y : I ⥤ Type u}
  {E : SSet.{u + 1}}
  (φ : X ⟶ Y) (F : (SSet.uliftFunctor.{u + 1, u}).obj (nerve I) ⟶ E)

/-- 要素の圏に沿う制限を、頂点と図式を固定した錐の族へ移す。 -/
def sectionsConeFamilyRestriction (x : E _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fixedEndpointConeSpace (_root_.SerrePositivity.InfinityCategories.Project.SetWeightedTensors.SetWeight.diagram Y F) x ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fixedEndpointConeSpace (_root_.SerrePositivity.InfinityCategories.Project.SetWeightedTensors.SetWeight.diagram X F) x :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.normalizedEndpointConeRestriction (_root_.SerrePositivity.InfinityCategories.Project.SetWeightedTensors.SetWeight.diagram Y F) (_root_.SerrePositivity.InfinityCategories.Project.SetWeightedTensors.SetWeight.diagram X F) (_root_.SerrePositivity.InfinityCategories.Project.SetWeightedTensors.SetWeight.elementsMap φ)
    (_root_.SerrePositivity.InfinityCategories.Project.SetWeightedTensors.SetWeight.elementsMap_diagram φ F) x

/-- 切断の制限と錐の族への比較は、全パラメータで厳密に可換。 -/
lemma sectionsConeFamilyRestriction_fromSections (x : E _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorPre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (SSet.yonedaEquiv.symm x))
        (_root_.SerrePositivity.InfinityCategories.Project.SetWeightedTensors.SetWeight.diagram Y F) (_root_.SerrePositivity.InfinityCategories.Project.SetWeightedTensors.SetWeight.elementsMap φ) ≫
      eqToHom (congrArg (fun r => _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.coherentConeSectionSpace r x)
        (_root_.SerrePositivity.InfinityCategories.Project.SetWeightedTensors.SetWeight.elementsMap_diagram φ F))) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.sectionEndpointConeComparison (_root_.SerrePositivity.InfinityCategories.Project.SetWeightedTensors.SetWeight.diagram X F) x =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.sectionEndpointConeComparison (_root_.SerrePositivity.InfinityCategories.Project.SetWeightedTensors.SetWeight.diagram Y F) x ≫
        sectionsConeFamilyRestriction φ F x :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.normalizedSectionEndpointComparison_restrict (_root_.SerrePositivity.InfinityCategories.Project.SetWeightedTensors.SetWeight.diagram Y F) (_root_.SerrePositivity.InfinityCategories.Project.SetWeightedTensors.SetWeight.diagram X F)
    (_root_.SerrePositivity.InfinityCategories.Project.SetWeightedTensors.SetWeight.elementsMap φ) (_root_.SerrePositivity.InfinityCategories.Project.SetWeightedTensors.SetWeight.elementsMap_diagram φ F) x

end SetWeight
end SerrePositivity.InfinityCategories.Project.SetWeightedTensors
