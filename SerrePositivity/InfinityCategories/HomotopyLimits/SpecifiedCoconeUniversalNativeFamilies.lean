module

public import
  SerrePositivity.InfinityCategories.HomotopyLimits.SpecifiedCoconeUniversalNativeParameters

/-!
概要：native 普遍 span の全図式族を、元の指定余錐と同じ全 Hom パラメータで表示する。
方針：同じ頂点等式を前合成し、終端の点図式だけを正規化して同じ base 逆を回収する。
規約：元の native 全族を保持。使われ方：同じ終端係数を持つ rooted 全族との比較。
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
local notation "s" => partialColimitStrictSpanCocone c hc f (i ≫ p) rfl dB
  g (j ≫ p) (coconePushoutBoundary_eq hp p) dC
local notation "q" => sliceUnderProjection p
local notation "r" => sliceUnderProjection (strictCoherentDiagram
  (partialColimitApexSpan c hc f (i ≫ p) rfl dB
    g (j ≫ p) (coconePushoutBoundary_eq hp p) dC))
local notation "U" => specifiedCoconeUniversalNativeParameter hp p c hc dB dC y
local notation "he" => specifiedCoconeUniversalNativePointDiagram hp p c hc dB dC

section
local notation "σ" => SSet.yonedaEquiv.symm (SSet.Edge.CompStruct.simplex
  (partialColimitSpanLeftTriangle c hc f (i ≫ p) rfl dB
    g (j ≫ p) (coconePushoutBoundary_eq hp p) dC))
local notation "v" => stdSimplex.δ (0 : Fin 2) ≫ stdSimplex.δ (0 : Fin 3)
local notation "ht" => nativeSpanLeftHomDiagram_tip hp p c hc dB dC
local notation "G" => nativeSpanLeftUniversalHomDiagramFamily hp p c hc dB dC y

/-- 同じ左の native 図式の終端を、元の指定余錐の点図式表示へ揃える。 -/
lemma specifiedCoconeLeftUniversalNative_tip : v ≫ σ = coconeVertexDiagram d :=
  (ht).trans (he).symm

/-- 元の指定余錐の全 Hom パラメータで表示した、同じ左の native 普遍全族。 -/
def specifiedCoconeLeftUniversalNativeFamily :
    pinchedHomLeft (JoinCocone.vertex d) y ⟶ coconeMappingSpace σ y := U ≫ G

/-- 共通パラメータでの native 普遍全族の終端は、元の指定余錐の同じ全 Hom の係数。 -/
lemma specifiedCoconeLeftUniversalNativeFamily_terminal :
    specifiedCoconeLeftUniversalNativeFamily hp p c hc dB dC y ≫
        normalizedCoconeRestrictionFiber σ v
          (specifiedCoconeLeftUniversalNative_tip hp p c hc dB dC) y =
      (leftFibrationInitialBaseIso q d y).inv := by
  have hr := normalizedCoconeRestrictionFiber_targetEq σ v
    (coconeVertexDiagram s) (coconeVertexDiagram d) ht
    (specifiedCoconeLeftUniversalNative_tip hp p c hc dB dC) (he).symm y
  calc
    _ = (U ≫ (G ≫ normalizedCoconeRestrictionFiber σ v ht y)) ≫
        eqToHom (congrArg (fun a ↦ coconeMappingSpace a y) (he).symm) := by
      exact (Category.assoc U G (normalizedCoconeRestrictionFiber σ v
        (specifiedCoconeLeftUniversalNative_tip hp p c hc dB dC) y)).trans
          ((congrArg (fun m ↦ U ≫ (G ≫ m)) hr).trans (by simp only [Category.assoc]))
    _ = (U ≫ (leftFibrationInitialBaseIso r s y).inv) ≫
        eqToHom (congrArg (fun a ↦ coconeMappingSpace a y) (he).symm) :=
      congrArg (fun m ↦ (U ≫ m) ≫
        eqToHom (congrArg (fun a ↦ coconeMappingSpace a y) (he).symm))
          (nativeSpanLeftUniversalHomDiagramFamily_terminal hp p c hc dB dC y)
    _ = _ := by
      rw [specifiedCoconeUniversalNativeParameter_terminal]
      simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]
end

section
local notation "σ" => stdSimplex.σ (2 : Fin 3) ≫ SSet.yonedaEquiv.symm (SSet.Edge.CompStruct.simplex
  (partialColimitSpanRightTriangle c hc f (i ≫ p) rfl dB
    g (j ≫ p) (coconePushoutBoundary_eq hp p) dC))
local notation "v" => (stdSimplex.δ (0 : Fin 2) ≫ stdSimplex.δ (0 : Fin 3)) ≫
  stdSimplex.δ (0 : Fin 4)
local notation "ht" => nativeSpanRightHomDiagram_tip hp p c hc dB dC
local notation "G" => nativeSpanRightUniversalHomDiagramFamily hp p c hc dB dC y

/-- 同じ右の native 図式の終端を、元の指定余錐の点図式表示へ揃える。 -/
lemma specifiedCoconeRightUniversalNative_tip : v ≫ σ = coconeVertexDiagram d :=
  (ht).trans (he).symm

/-- 元の指定余錐の全 Hom パラメータで表示した、同じ右の native 普遍全族。 -/
def specifiedCoconeRightUniversalNativeFamily :
    pinchedHomLeft (JoinCocone.vertex d) y ⟶ coconeMappingSpace σ y := U ≫ G

/-- 共通パラメータでの native 普遍全族の終端は、元の指定余錐の同じ全 Hom の係数。 -/
lemma specifiedCoconeRightUniversalNativeFamily_terminal :
    specifiedCoconeRightUniversalNativeFamily hp p c hc dB dC y ≫
        normalizedCoconeRestrictionFiber σ v
          (specifiedCoconeRightUniversalNative_tip hp p c hc dB dC) y =
      (leftFibrationInitialBaseIso q d y).inv := by
  have hr := normalizedCoconeRestrictionFiber_targetEq σ v
    (coconeVertexDiagram s) (coconeVertexDiagram d) ht
    (specifiedCoconeRightUniversalNative_tip hp p c hc dB dC) (he).symm y
  calc
    _ = (U ≫ (G ≫ normalizedCoconeRestrictionFiber σ v ht y)) ≫
        eqToHom (congrArg (fun a ↦ coconeMappingSpace a y) (he).symm) := by
      exact (Category.assoc U G (normalizedCoconeRestrictionFiber σ v
        (specifiedCoconeRightUniversalNative_tip hp p c hc dB dC) y)).trans
          ((congrArg (fun m ↦ U ≫ (G ≫ m)) hr).trans (by simp only [Category.assoc]))
    _ = (U ≫ (leftFibrationInitialBaseIso r s y).inv) ≫
        eqToHom (congrArg (fun a ↦ coconeMappingSpace a y) (he).symm) :=
      congrArg (fun m ↦ (U ≫ m) ≫
        eqToHom (congrArg (fun a ↦ coconeMappingSpace a y) (he).symm))
          (nativeSpanRightUniversalHomDiagramFamily_terminal hp p c hc dB dC y)
    _ = _ := by
      rw [specifiedCoconeUniversalNativeParameter_terminal]
      simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]
end

end
end SerrePositivity.InfinityCategories.HomotopyLimits
