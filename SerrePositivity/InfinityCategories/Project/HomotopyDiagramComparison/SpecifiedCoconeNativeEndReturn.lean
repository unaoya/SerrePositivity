module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.StrictSpanPointHomEndReturn
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.CoconePointFullHomFamily
public import
  SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SpecifiedCoconeUniversalNativeParameters

/-!
概要：元の native 普遍族の共通 path end 比較を、同じ選択済み全余錐族の辺全族 end へ戻す。
方針：元の点 Hom end で因数分解し、同じ逆の余単位と全余錐族の制限式を使う。
規約：元の逆・普遍族・パラメータを保持。使われ方：指定経路の正方形との照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
noncomputable section
attribute [local irreducible] _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitStrictSpanCocone _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitApexSpan
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpanRootLeg _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpanLeftLeg _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpanRightLeg
variable {A B C D : SSet.{u + 1}} {f : A ⟶ B} {g : A ⟶ C}
  {i : B ⟶ D} {j : C ⟶ D} (hp : IsPushout f g i j) [Mono g] (p : D ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})
  (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (f ≫ (i ≫ p))) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c)
  (dB : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (i ≫ p)) (dC : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (j ≫ p)) (y : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} _⦋0⦌)
local notation "d" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpecifiedPathCocone hp p c hc dB dC
local notation "s" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitStrictSpanCocone c hc f (i ≫ p) rfl dB
  g (j ≫ p) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconePushoutBoundary_eq hp p) dC
local notation "F" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitApexSpan c hc f (i ≫ p) rfl dB
  g (j ≫ p) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconePushoutBoundary_eq hp p) dC
local notation "q" => _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram F
local notation "h" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.strictSpanHornDiagram q
local notation "r" => _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cosliceRestrictionFiberMap q (Iso.inv _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.strictSpanHornIso) y
local notation "U" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeUniversalNativeParameter hp p c hc dB dC y
local notation "a" => U ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconePointHomFamily s y
local notation "full" => U ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconePointFullHomFiberFamily s y
local notation "res" => _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.normalizedCoconeRestrictionFiber (Subtype.val s)
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl _ Δ[0])
  (Subtype.property s) y

/-- 元の native path end 比較に含まれる、選択済み逆を使う同じ点 Hom end の族。 -/
def specifiedCoconeNativePointHomEndFamily :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomLeft (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone.vertex d) y ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSections (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight (AsSmall.{u + 1} WalkingCospan))
        (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.spanPointHomCospan h y) :=
  a ≫ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.strictSpanCoconeToPointHomEnd q y

/-- 同じ元の選択済み全余錐族から、図式への制限と horn 表示を経た辺全族 end の族。 -/
def specifiedCoconeNativeEdgeEndFamily :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomLeft (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone.vertex d) y ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSections (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight (AsSmall.{u + 1} WalkingCospan))
        (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.spanEdgeCoconeCospan h y) :=
  (full ≫ res) ≫ r ≫ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.spanCoconeToEdgeEnd h y

/-- 元の native path end 比較は、同じ点 Hom end の族と既存の表示比較で因数分解する。 -/
lemma specifiedCoconeNativeFamilyToPathEnd_factor :
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeNativeFamilyToPathEnd hp p c hc dB dC y =
      specifiedCoconeNativePointHomEndFamily hp p c hc dB dC y ≫
        (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpanHomEndIso hp p c hc dB dC y).hom ≫
          _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitHomEndToPathEnd hp p y c hc dB dC := by
  simp only [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeNativeFamilyToPathEnd, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.nativeSpanUniversalFamilyToPathEnd,
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpanCoconeToHomEnd, specifiedCoconeNativePointHomEndFamily,
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeUniversalNativeParameter, Category.assoc]

/-- 元の逆の余単位で辺全族へ戻すと、同じ普遍全余錐族の同じ制限へホモトピック。 -/
def specifiedCoconeNativePointHomEndReturn : SSet.Homotopy
    (specifiedCoconeNativePointHomEndFamily hp p c hc dB dC y ≫ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.spanPointHomToEdgeEnd h y)
    (specifiedCoconeNativeEdgeEndFamily hp p c hc dB dC y) :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.homotopyEndpointTransport (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.strictSpanPointHomEndFamilyReturn q y a) rfl (by
    have ha : a = full ≫ res := by
      exact (congrArg (U ≫ ·) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconePointFullHomFiberFamily_restriction s y).symm).trans
        (Category.assoc U (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconePointFullHomFiberFamily s y) res).symm
    exact congrArg (fun k ↦ k ≫ r ≫ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.spanCoconeToEdgeEnd h y) ha)

/-- 戻し円柱は、同じ元の native Hom 族を元の strict 戻しに前合成した raw な射。 -/
lemma specifiedCoconeNativePointHomEndReturn_raw :
    (specifiedCoconeNativePointHomEndReturn hp p c hc dB dC y).h =
      (a ▷ (Δ[1] : SSet.{u + 1})) ≫ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.strictSpanPointHomEndReturn q y).h := by
  exact (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.homotopyEndpointTransport_raw _ _ _).trans
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.strictSpanPointHomEndFamilyReturn_raw q y a)

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
