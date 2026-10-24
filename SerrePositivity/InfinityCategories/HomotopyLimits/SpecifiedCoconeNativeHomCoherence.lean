module

public import SerrePositivity.InfinityCategories.HomotopyLimits.SpecifiedCoconeRootHomCoherence
public import SerrePositivity.InfinityCategories.HomotopyLimits.SpecifiedCoconeLeftNativeComparison
public import SerrePositivity.InfinityCategories.HomotopyLimits.SpecifiedCoconeRightNativeComparison

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
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section
attribute [local irreducible] partialColimitStrictSpanCocone partialColimitApexSpan
  partialColimitSpanRootLeg partialColimitSpanLeftLeg partialColimitSpanRightLeg
variable {A B C D : SSet.{u + 1}} {f : A ⟶ B} {g : A ⟶ C}
  {i : B ⟶ D} {j : C ⟶ D} (hp : IsPushout f g i j) [Mono g] (p : D ⟶ SpaceInfinity.{u})
  (c : JoinCocone (f ≫ (i ≫ p))) (hc : IsColimitCone c)
  (dB : JoinCocone (i ≫ p)) (hB : IsColimitCone dB)
  (dC : JoinCocone (j ≫ p)) (hC : IsColimitCone dC) (y : SpaceInfinity.{u} _⦋0⦌)
local notation "PL" => specifiedCoconeLeftProjectedCylinder hp p c hc dB hB dC y
local notation "PR" => specifiedCoconeRightProjectedCylinder hp p c hc dB dC hC y
local notation "TL" => specifiedCoconeLeftRestrictionHomComparison hp p c hc dB hB dC y
local notation "TR" => specifiedCoconeRightRestrictionRootedHomComparison hp p c hc dB dC hC y
local notation "NL" => specifiedCoconeLeftRootNativeCylinder hp p c hc dB dC y
local notation "NR" => specifiedCoconeRootNativeCylinder hp p c hc dB dC y
local notation "IL" => specifiedCoconeLeftNativeIso hp p c hc dB hB dC y
local notation "IR" => specifiedCoconeRightNativeIso hp p c hc dB dC hC y
local notation "UL" => coconePointHomFamily
  (partialColimitSpecifiedPathCocone hp p c hc dB dC) y ≫ cosliceRestrictionFiberMap p i y
local notation "UR" => specifiedCoconeRightHomRestriction hp p c hc dB dC y
local notation "HL" => functorHomotopyPrecomp (partialColimitHomEndLeftCylinder p y c hc dB hB) UL
local notation "HR" => functorHomotopyPrecomp
  (partialColimitHomEndRightCylinder hp p y c hc dC hC) UR
local notation "cls(" H ")" => SSet.Truncated.HomotopyCategory.homMk
  (functorEdgeOfSimplicialHomotopy H)

/-- 左右の元の中間円柱から native な共通脚へ至る三因子の積は一致する。 -/
lemma specifiedCoconeProjectedNativeHom_comp :
    cls(PL) ≫ (cls(TL) ≫ cls(NL)) = cls(PR) ≫ (cls(TR) ≫ cls(NR)) := by
  have hL := specifiedCoconeLeftRestrictionTriangle_homMk_comp hp p c hc dB hB dC y
  have hR := specifiedCoconeRightRootedTriangle_homMk_comp hp p c hc dB dC hC y
  exact (Category.assoc (cls(PL)) (cls(TL)) (cls(NL))).symm.trans
    ((congrArg (· ≫ cls(NL)) hL).trans
      ((specifiedCoconeRootHomCylinder_native_comp hp p c hc dB dC y).trans
        ((congrArg (· ≫ cls(NR)) hR.symm).trans
          (Category.assoc (cls(PR)) (cls(TR)) (cls(NR))))))

/-- 共通 end の元の左右の円柱と、公開した native 比較同型の積は同じ Arrow である。 -/
lemma specifiedCoconeNativeHom_comp_hom_arrow :
    Arrow.mk (cls(HL) ≫ (IL).hom) = Arrow.mk (cls(HR) ≫ (IR).hom) := by
  have hL := SerrePositivity.InfinityCategories.functorHomotopy_hom_arrow_of_h_eq PL HL
    (specifiedCoconeLeftProjectedCylinder_raw hp p c hc dB hB dC y)
  have hR := SerrePositivity.InfinityCategories.functorHomotopy_hom_arrow_of_h_eq PR HR
    (specifiedCoconeRightProjectedCylinder_raw hp p c hc dB dC hC y)
  have hIL : Arrow.mk (IL).hom = Arrow.mk (cls(TL) ≫ cls(NL)) :=
    SerrePositivity.InfinityCategories.functorIsoTransport_hom_arrow _ _ _
  have hIR : Arrow.mk (IR).hom = Arrow.mk (cls(TR) ≫ cls(NR)) :=
    SerrePositivity.InfinityCategories.functorIsoTransport_hom_arrow _ _ _
  exact (arrowComposition_congr hL.symm hIL).trans
    ((congrArg Arrow.mk
      (specifiedCoconeProjectedNativeHom_comp hp p c hc dB hB dC hC y)).trans
        (arrowComposition_congr hR.symm hIR).symm)

end
end SerrePositivity.InfinityCategories.HomotopyLimits
