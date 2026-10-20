module

public import
  SerrePositivity.InfinityCategories.HomotopyLimits.SpecifiedCoconeUniversalNativeFamilies
public import SerrePositivity.InfinityCategories.HomotopyLimits.SpecifiedCoconeNativeBaseDiagrams
public import SerrePositivity.InfinityCategories.HomotopyLimits.SpecifiedCoconeRootPrecomposition
public import
  SerrePositivity.InfinityCategories.HomotopyLimits.NormalizedCosliceRestrictionComposition

/-!
概要：元の rooted 全族の最後の頂点係数を、同じ指定余錐の全 Hom 表示へ厳密に回収する。
方針：同じ native 全族の根辺とその終端の二段制限を合成する。
規約：元の根辺全族を保持。使われ方：native 普遍全族との同じ終端上での比較。
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
  (dB : JoinCocone (i ≫ p)) (dC : JoinCocone (j ≫ p)) (y : SpaceInfinity.{u} _⦋0⦌)
local notation "d" => partialColimitSpecifiedPathCocone hp p c hc dB dC
local notation "root" => specifiedCoconeNativeRootEdge hp p c hc dB dC
local notation "rt" => specifiedCoconeNativeRootEdge_target hp p c hc dB dC
local notation "Q" => Iso.inv (leftFibrationInitialBaseIso (sliceUnderProjection p) d y)

section
local notation "σ" => SSet.yonedaEquiv.symm (SSet.Edge.CompStruct.simplex
  (partialColimitSpanLeftTriangle c hc f (i ≫ p) rfl dB
    g (j ≫ p) (coconePushoutBoundary_eq hp p) dC))
local notation "v" => stdSimplex.δ (0 : Fin 2) ≫ stdSimplex.δ (0 : Fin 3)
local notation "N" => specifiedCoconeLeftNativeBaseDiagramFamily hp p c hc dB dC y
local notation "hr" => specifiedCoconeLeftNativeBaseDiagram_root hp p c hc dB dC
local notation "ht" => specifiedCoconeLeftUniversalNative_tip hp p c hc dB dC

/-- 左の元の rooted 全族の終端係数は、native 普遍族と同じ元の全 Hom の係数である。 -/
lemma specifiedCoconeLeftNativeBaseDiagramFamily_terminal :
    N ≫ normalizedCoconeRestrictionFiber σ v ht y = Q := by
  have hcomp := normalizedCoconeRestrictionFiber_twoStep σ (stdSimplex.δ (1 : Fin 3)) root hr
    (stdSimplex.δ (0 : Fin 2)) (coconeVertexDiagram d) rt v
    triangleTip_longEdge.symm ht y
  calc
    _ = N ≫ (normalizedCoconeRestrictionFiber σ (stdSimplex.δ (1 : Fin 3)) hr y ≫
        normalizedCoconeRestrictionFiber root (stdSimplex.δ (0 : Fin 2)) rt y) :=
      congrArg (N ≫ ·) hcomp.symm
    _ = (N ≫ normalizedCoconeRestrictionFiber σ (stdSimplex.δ (1 : Fin 3)) hr y) ≫
        normalizedCoconeRestrictionFiber root (stdSimplex.δ (0 : Fin 2)) rt y :=
      (Category.assoc _ _ _).symm
    _ = specifiedCoconeLeftRootBaseEdgeFiberFamily hp p c hc dB dC y ≫
        normalizedCoconeRestrictionFiber root (stdSimplex.δ (0 : Fin 2)) rt y :=
      congrArg (· ≫ normalizedCoconeRestrictionFiber root (stdSimplex.δ (0 : Fin 2)) rt y)
        (specifiedCoconeLeftNativeBaseDiagramFamily_root hp p c hc dB dC y)
    _ = _ := specifiedCoconeLeftRootBaseEdgeFiberFamily_target hp p c hc dB dC y
end

section
local notation "σ" => stdSimplex.σ (2 : Fin 3) ≫ SSet.yonedaEquiv.symm (SSet.Edge.CompStruct.simplex
  (partialColimitSpanRightTriangle c hc f (i ≫ p) rfl dB
    g (j ≫ p) (coconePushoutBoundary_eq hp p) dC))
local notation "v" => (stdSimplex.δ (0 : Fin 2) ≫ stdSimplex.δ (0 : Fin 3)) ≫
  stdSimplex.δ (0 : Fin 4)
local notation "N" => specifiedCoconeRightNativeBaseDiagramFamily hp p c hc dB dC y
local notation "hr" => specifiedCoconeRightNativeBaseDiagram_root hp p c hc dB dC
local notation "ht" => specifiedCoconeRightUniversalNative_tip hp p c hc dB dC

/-- 右の元の rooted 全族の終端係数は、native 普遍族と同じ元の全 Hom の係数である。 -/
lemma specifiedCoconeRightNativeBaseDiagramFamily_terminal :
    N ≫ normalizedCoconeRestrictionFiber σ v ht y = Q := by
  have hcomp := normalizedCoconeRestrictionFiber_twoStep σ (tetrahedronRootEdge) root hr
    (stdSimplex.δ (0 : Fin 2)) (coconeVertexDiagram d) rt v
    tetrahedronRootEdge_target_terminalFace ht y
  calc
    _ = N ≫ (normalizedCoconeRestrictionFiber σ (tetrahedronRootEdge) hr y ≫
        normalizedCoconeRestrictionFiber root (stdSimplex.δ (0 : Fin 2)) rt y) :=
      congrArg (N ≫ ·) hcomp.symm
    _ = (N ≫ normalizedCoconeRestrictionFiber σ (tetrahedronRootEdge) hr y) ≫
        normalizedCoconeRestrictionFiber root (stdSimplex.δ (0 : Fin 2)) rt y :=
      (Category.assoc _ _ _).symm
    _ = specifiedCoconeRootBaseEdgeFiberFamily hp p c hc dB dC y ≫
        normalizedCoconeRestrictionFiber root (stdSimplex.δ (0 : Fin 2)) rt y :=
      congrArg (· ≫ normalizedCoconeRestrictionFiber root (stdSimplex.δ (0 : Fin 2)) rt y)
        (specifiedCoconeRightNativeBaseDiagramFamily_root hp p c hc dB dC y)
    _ = _ := specifiedCoconeRootBaseEdgeFiberFamily_target hp p c hc dB dC y
end

end
end SerrePositivity.InfinityCategories.HomotopyLimits
