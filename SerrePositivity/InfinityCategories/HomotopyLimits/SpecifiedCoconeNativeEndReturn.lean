module

public import SerrePositivity.InfinityCategories.HomotopyLimits.StrictSpanPointHomEndReturn
public import SerrePositivity.InfinityCategories.HomotopyLimits.CoconePointFullHomFamily
public import
  SerrePositivity.InfinityCategories.HomotopyLimits.SpecifiedCoconeUniversalNativeParameters

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
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section
attribute [local irreducible] partialColimitStrictSpanCocone partialColimitApexSpan
  partialColimitSpanRootLeg partialColimitSpanLeftLeg partialColimitSpanRightLeg
variable {A B C D : SSet.{u + 1}} {f : A ⟶ B} {g : A ⟶ C}
  {i : B ⟶ D} {j : C ⟶ D} (hp : IsPushout f g i j) [Mono g] (p : D ⟶ SpaceInfinity.{u})
  (c : JoinCocone (f ≫ (i ≫ p))) (hc : IsColimitCone c)
  (dB : JoinCocone (i ≫ p)) (dC : JoinCocone (j ≫ p)) (y : SpaceInfinity.{u} _⦋0⦌)
local notation "d" => partialColimitSpecifiedPathCocone hp p c hc dB dC
local notation "s" => partialColimitStrictSpanCocone c hc f (i ≫ p) rfl dB
  g (j ≫ p) (coconePushoutBoundary_eq hp p) dC
local notation "F" => partialColimitApexSpan c hc f (i ≫ p) rfl dB
  g (j ≫ p) (coconePushoutBoundary_eq hp p) dC
local notation "q" => strictCoherentDiagram F
local notation "h" => strictSpanHornDiagram q
local notation "r" => cosliceRestrictionFiberMap q (Iso.inv strictSpanHornIso) y
local notation "U" => specifiedCoconeUniversalNativeParameter hp p c hc dB dC y
local notation "a" => U ≫ coconePointHomFamily s y
local notation "full" => U ≫ coconePointFullHomFiberFamily s y
local notation "res" => normalizedCoconeRestrictionFiber (Subtype.val s)
  (joinInl _ Δ[0])
  (Subtype.property s) y

/-- 元の native path end 比較に含まれる、選択済み逆を使う同じ点 Hom end の族。 -/
def specifiedCoconeNativePointHomEndFamily :
    pinchedHomLeft (JoinCocone.vertex d) y ⟶
      weightedSections (bousfieldKanWeight (AsSmall.{u + 1} WalkingCospan))
        (spanPointHomCospan h y) :=
  a ≫ strictSpanCoconeToPointHomEnd q y

/-- 同じ元の選択済み全余錐族から、図式への制限と horn 表示を経た辺全族 end の族。 -/
def specifiedCoconeNativeEdgeEndFamily :
    pinchedHomLeft (JoinCocone.vertex d) y ⟶
      weightedSections (bousfieldKanWeight (AsSmall.{u + 1} WalkingCospan))
        (spanEdgeCoconeCospan h y) :=
  (full ≫ res) ≫ r ≫ spanCoconeToEdgeEnd h y

/-- 元の native path end 比較は、同じ点 Hom end の族と既存の表示比較で因数分解する。 -/
lemma specifiedCoconeNativeFamilyToPathEnd_factor :
    specifiedCoconeNativeFamilyToPathEnd hp p c hc dB dC y =
      specifiedCoconeNativePointHomEndFamily hp p c hc dB dC y ≫
        (partialColimitSpanHomEndIso hp p c hc dB dC y).hom ≫
          partialColimitHomEndToPathEnd hp p y c hc dB dC := by
  simp only [specifiedCoconeNativeFamilyToPathEnd, nativeSpanUniversalFamilyToPathEnd,
    partialColimitSpanCoconeToHomEnd, specifiedCoconeNativePointHomEndFamily,
    specifiedCoconeUniversalNativeParameter, Category.assoc]

/-- 元の逆の余単位で辺全族へ戻すと、同じ普遍全余錐族の同じ制限へホモトピック。 -/
def specifiedCoconeNativePointHomEndReturn : SSet.Homotopy
    (specifiedCoconeNativePointHomEndFamily hp p c hc dB dC y ≫ spanPointHomToEdgeEnd h y)
    (specifiedCoconeNativeEdgeEndFamily hp p c hc dB dC y) :=
  homotopyEndpointTransport (strictSpanPointHomEndFamilyReturn q y a) rfl (by
    have ha : a = full ≫ res := by
      exact (congrArg (U ≫ ·) (coconePointFullHomFiberFamily_restriction s y).symm).trans
        (Category.assoc U (coconePointFullHomFiberFamily s y) res).symm
    exact congrArg (fun k ↦ k ≫ r ≫ spanCoconeToEdgeEnd h y) ha)

/-- 戻し円柱は、同じ元の native Hom 族を元の strict 戻しに前合成した raw な射。 -/
lemma specifiedCoconeNativePointHomEndReturn_raw :
    (specifiedCoconeNativePointHomEndReturn hp p c hc dB dC y).h =
      (a ▷ (Δ[1] : SSet.{u + 1})) ≫ (strictSpanPointHomEndReturn q y).h := by
  exact (homotopyEndpointTransport_raw _ _ _).trans
    (strictSpanPointHomEndFamilyReturn_raw q y a)

end
end SerrePositivity.InfinityCategories.HomotopyLimits
