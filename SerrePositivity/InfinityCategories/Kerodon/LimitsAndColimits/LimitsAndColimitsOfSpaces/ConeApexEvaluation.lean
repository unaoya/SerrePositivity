module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.ConeSectionRestrictionCriterion
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.RelativeFunctorInitialEvaluation
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.FatJoinInitialComparison

/-!
概要：錐の図式上の coslice の切断を、錐の頂点で評価する。
方針：join の頂点包含の left anodyne 性を示し、相対関手の点評価へ適用する。
規約：錐は任意の coherent な錐。通常の圏の nerve に制限しない。
使われ方：HTT 4.2.4.1、Kerodon 7.4.1.6（Tag 05QS）、7.5.4.6（Tag 03BB） の豊穣比較の始域の同値検査。

対応節は Kerodon 7.4（Tag 02SX）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces

/-- 概要：錐の形の頂点からの包含は left anodyne。
方針：空集合への右因子の包含を点と join し、空因子の join の同型で前合成する。
規約：K は任意で、充填性や非空性は要求しない。
使われ方：Kerodon 7.4.1.6（Tag 05QS） の錐の図式上の切断の頂点評価。 -/
lemma joinApexInclusion_leftAnodyne (K : SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftAnodyneExtensions (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (Δ[0] : SSet.{u}) K) := by
  have : IsIso (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (Δ[0] : SSet.{u}) (⊥_ SSet.{u})) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isIso_joinInl_of_isInitial Δ[0] (⊥_ SSet.{u}) initialIsInitial
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftAnodyneExtensions.comp_mem
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (Δ[0] : SSet.{u}) (⊥_ SSet.{u}))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 (Δ[0] : SSet.{u})) (initial.to K))
    (MorphismProperty.of_isIso _ _) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.ConeAnodyne.joinPoint_mono_leftAnodyne (initial.to K))
  simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl_joinMap, Category.id_comp] using h

/-- 概要：join による錐の形の左頂点。
方針：標準零単体の唯一の頂点を左包含で写す。
規約：型は join Δ[0] K の零単体。
使われ方：Kerodon 7.4.1.6（Tag 05QS） の相対関手の頂点評価の指定。 -/
def joinApexVertex (K : SSet.{u}) : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[0] : SSet.{u}) K) _⦋0⦌ :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (Δ[0] : SSet.{u}) K).app (Opposite.op ⦋0⦌) (SSet.stdSimplex.obj₀Equiv.symm 0)

/-- 概要：錐の図式は錐の形の左頂点を元の錐の頂点へ写す。
方針：錐の頂点の Yoneda 表示を零単体で評価する。
規約：頂点の厳密な等号。
使われ方：Kerodon 7.4.1.6（Tag 05QS） の評価射の終域の正規化。 -/
lemma coneDiagram_apex {K X : SSet.{u}} {p : K ⟶ X} (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p) :
    c.val.app (Opposite.op ⦋0⦌) (joinApexVertex K) = c.vertex := by
  have h : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (Δ[0] : SSet.{u}) K ≫ c.val = SSet.const c.vertex := by
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone.vertex_eq, ← SSet.yonedaEquiv_symm_zero, Equiv.symm_apply_apply]
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (Δ[0] : SSet.{u}) K ≫ c.val).app (Opposite.op ⦋0⦌)
    (SSet.stdSimplex.obj₀Equiv.symm 0) = c.vertex
  rw [h]
  simp [SSet.const]

/-- 概要：錐の図式上の切断を錐の頂点で評価する実際の射。
方針：相対関手の評価を行い、底の頂点の等号で終域を正規化する。
規約：終域は x の coslice の c.vertex 上の fiber。
使われ方：HTT 4.2.4.1 の豊穣 Hom からの切断比較の始域の検査。 -/
def coneApexSectionEvaluation {K X : SSet.{u}} {p : K ⟶ X}
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p) (x : X _⦋0⦌) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.coherentConeSectionSpace c.val x ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (SSet.yonedaEquiv.symm x)) c.vertex :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorEvaluate (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (SSet.yonedaEquiv.symm x)) c.val
    (joinApexVertex K) ≫ eqToHom (congrArg
      (fun y : X _⦋0⦌ ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (SSet.yonedaEquiv.symm x)) y)
      (coneDiagram_apex c))

/-- 概要：錐の頂点評価の包含後の値は通常の内部 Hom の頂点評価。
方針：頂点の等号による移送を消去し、相対評価の包含の式を使う。
規約：全パラメータの射の厳密な等式。
使われ方：Kerodon 7.4.1.6（Tag 05QS） の実際の豊穣比較の頂点での値の同定。 -/
lemma coneApexSectionEvaluation_ι {K X : SSet.{u}} {p : K ⟶ X}
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p) (x : X _⦋0⦌) :
    coneApexSectionEvaluation c x ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (SSet.yonedaEquiv.symm x)) c.vertex =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι ((ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[0] : SSet.{u}) K)).map
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (SSet.yonedaEquiv.symm x))) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex c.val) ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (joinApexVertex K) := by
  have ht {E B : SSet.{u}} (q : E ⟶ B) {y z : B _⦋0⦌} (h : y = z) :
      eqToHom (congrArg (fun b : B _⦋0⦌ ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber q b) h) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι q z =
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι q y := by cases h; exact Category.id_comp _
  rw [coneApexSectionEvaluation, Category.assoc, ht _ (coneDiagram_apex c),
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorEvaluate_ι]

/-- 概要：quasicategory では錐の図式上の切断の頂点評価は trivial Kan fibration。
方針：頂点包含の left anodyne 性と coslice の left fibration 性を相対評価に適用する。
規約：添字 K と coherent な錐 c は任意。
使われ方：HTT 4.2.4.1 の豊穣比較の始域の同値性の証明。 -/
lemma coneApexSectionEvaluation_trivialKanFibration {K X : SSet.{u}} [Quasicategory X]
    {p : K ⟶ X} (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p) (x : X _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (coneApexSectionEvaluation c x) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorEvaluate_trivialKanFibration_of_identification
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (SSet.yonedaEquiv.symm x)) c.val (joinApexVertex K) c.vertex
    (coneDiagram_apex c) (coneApexSectionEvaluation c x) (coneApexSectionEvaluation_ι c x)
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorEvaluate_trivialKanFibration_of_pointMap _ c.val
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (Δ[0] : SSet.{u}) K) (joinApexInclusion_leftAnodyne K)

/-- 概要：quasicategory では錐の図式上の切断の頂点評価は単体的ホモトピー同値。
方針：Kan 複体の間の trivial Kan fibration の同値性を使う。
規約：全ての coherent な錐に適用する。
使われ方：HTT 4.2.4.1 の豊穣比較の始域の二対三則。 -/
lemma coneApexSectionEvaluation_homotopyEquivalence {K X : SSet.{u}} [Quasicategory X]
    {p : K ⟶ X} (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p) (x : X _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (coneApexSectionEvaluation c x) := by
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_kanComplex_of_leftFibration
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (SSet.yonedaEquiv.symm x)) c.vertex
  have := coneApexSectionEvaluation_trivialKanFibration c x
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.qCatEquivalenceOfTrivialKanFibration (coneApexSectionEvaluation c x)).isQCatEquivalence
    |>.isSimplicialHomotopyEquivalence

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces
