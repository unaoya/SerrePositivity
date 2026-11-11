module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SpecifiedCoconeRootHomCoherence
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SpecifiedCoconeLeftNativeComparison
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SpecifiedCoconeRightNativeComparison

/-!
概要：共通 end の元の左右の Hom 円柱と、native な共通脚への比較の合成を照合する。
方針：同じ三角形の合成則をつなぎ、端点の輸送と raw な円柱の表示変更を Arrow で吸収する。
規約：元の円柱と指定された同型の類を保持。使われ方：共通 path end 内のホモトピー。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
noncomputable section
attribute [local irreducible] _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitStrictSpanCocone _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitApexSpan
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpanRootLeg _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpanLeftLeg _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpanRightLeg
variable {A B C D : SSet.{u + 1}} {f : A ⟶ B} {g : A ⟶ C}
  {i : B ⟶ D} {j : C ⟶ D} (hp : IsPushout f g i j) [Mono g] (p : D ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})
  (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (f ≫ (i ≫ p))) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c)
  (dB : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (i ≫ p)) (hB : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone dB)
  (dC : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (j ≫ p)) (hC : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone dC) (y : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} _⦋0⦌)
local notation "PL" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeLeftProjectedCylinder hp p c hc dB hB dC y
local notation "PR" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRightProjectedCylinder hp p c hc dB dC hC y
local notation "TL" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeLeftRestrictionHomComparison hp p c hc dB hB dC y
local notation "TR" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRightRestrictionRootedHomComparison hp p c hc dB dC hC y
local notation "NL" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeLeftRootNativeCylinder hp p c hc dB dC y
local notation "NR" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRootNativeCylinder hp p c hc dB dC y
local notation "IL" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeLeftNativeIso hp p c hc dB hB dC y
local notation "IR" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRightNativeIso hp p c hc dB dC hC y
local notation "UL" => _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconePointHomFamily
  (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpecifiedPathCocone hp p c hc dB dC) y ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cosliceRestrictionFiberMap p i y
local notation "UR" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRightHomRestriction hp p c hc dB dC y
local notation "HL" => _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitHomEndLeftCylinder p y c hc dB hB) UL
local notation "HR" => _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp
  (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitHomEndRightCylinder hp p y c hc dC hC) UR
local notation "cls(" H ")" => SSet.Truncated.HomotopyCategory.homMk
  (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H)

/-- 左右の元の中間円柱から native な共通脚へ至る三因子の積は一致する。 -/
lemma specifiedCoconeProjectedNativeHom_comp :
    cls(PL) ≫ (cls(TL) ≫ cls(NL)) = cls(PR) ≫ (cls(TR) ≫ cls(NR)) := by
  have hL := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeLeftRestrictionTriangle_homMk_comp hp p c hc dB hB dC y
  have hR := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRightRootedTriangle_homMk_comp hp p c hc dB dC hC y
  exact (Category.assoc (cls(PL)) (cls(TL)) (cls(NL))).symm.trans
    ((congrArg (· ≫ cls(NL)) hL).trans
      ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRootHomCylinder_native_comp hp p c hc dB dC y).trans
        ((congrArg (· ≫ cls(NR)) hR.symm).trans
          (Category.assoc (cls(PR)) (cls(TR)) (cls(NR))))))

/-- 共通 end の元の左右の円柱と、公開した native 比較同型の積は同じ Arrow である。 -/
lemma specifiedCoconeNativeHom_comp_hom_arrow :
    Arrow.mk (cls(HL) ≫ (IL).hom) = Arrow.mk (cls(HR) ≫ (IR).hom) := by
  have hL := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomotopy_hom_arrow_of_h_eq PL HL
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeLeftProjectedCylinder_raw hp p c hc dB hB dC y)
  have hR := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomotopy_hom_arrow_of_h_eq PR HR
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRightProjectedCylinder_raw hp p c hc dB dC hC y)
  have hIL : Arrow.mk (IL).hom = Arrow.mk (cls(TL) ≫ cls(NL)) :=
    _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorIsoTransport_hom_arrow _ _ _
  have hIR : Arrow.mk (IR).hom = Arrow.mk (cls(TR) ≫ cls(NR)) :=
    _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorIsoTransport_hom_arrow _ _ _
  exact (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.arrowComposition_congr hL.symm hIL).trans
    ((congrArg Arrow.mk
      (specifiedCoconeProjectedNativeHom_comp hp p c hc dB hB dC hC y)).trans
        (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.arrowComposition_congr hR.symm hIR).symm)

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
