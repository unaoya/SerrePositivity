module

public import
  SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SpecifiedCocones.SpecifiedCoconeUniversalNativeParameters

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
local notation "q" => _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection p
local notation "r" => _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram
  (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitApexSpan c hc f (i ≫ p) rfl dB
    g (j ≫ p) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconePushoutBoundary_eq hp p) dC))
local notation "U" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeUniversalNativeParameter hp p c hc dB dC y
local notation "he" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeUniversalNativePointDiagram hp p c hc dB dC

section
local notation "σ" => SSet.yonedaEquiv.symm (SSet.Edge.CompStruct.simplex
  (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpanLeftTriangle c hc f (i ≫ p) rfl dB
    g (j ≫ p) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconePushoutBoundary_eq hp p) dC))
local notation "v" => stdSimplex.δ (0 : Fin 2) ≫ stdSimplex.δ (0 : Fin 3)
local notation "ht" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.nativeSpanLeftHomDiagram_tip hp p c hc dB dC
local notation "G" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.nativeSpanLeftUniversalHomDiagramFamily hp p c hc dB dC y

/-- 同じ左の native 図式の終端を、元の指定余錐の点図式表示へ揃える。 -/
lemma specifiedCoconeLeftUniversalNative_tip : v ≫ σ = _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeVertexDiagram d :=
  (ht).trans (he).symm

/-- 元の指定余錐の全 Hom パラメータで表示した、同じ左の native 普遍全族。 -/
def specifiedCoconeLeftUniversalNativeFamily :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomLeft (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone.vertex d) y ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace σ y := U ≫ G

/-- 共通パラメータでの native 普遍全族の終端は、元の指定余錐の同じ全 Hom の係数。 -/
lemma specifiedCoconeLeftUniversalNativeFamily_terminal :
    specifiedCoconeLeftUniversalNativeFamily hp p c hc dB dC y ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.normalizedCoconeRestrictionFiber σ v
          (specifiedCoconeLeftUniversalNative_tip hp p c hc dB dC) y =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationInitialBaseIso q d y).inv := by
  have hr := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.normalizedCoconeRestrictionFiber_targetEq σ v
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeVertexDiagram s) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeVertexDiagram d) ht
    (specifiedCoconeLeftUniversalNative_tip hp p c hc dB dC) (he).symm y
  calc
    _ = (U ≫ (G ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.normalizedCoconeRestrictionFiber σ v ht y)) ≫
        eqToHom (congrArg (fun a ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace a y) (he).symm) := by
      exact (Category.assoc U G (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.normalizedCoconeRestrictionFiber σ v
        (specifiedCoconeLeftUniversalNative_tip hp p c hc dB dC) y)).trans
          ((congrArg (fun m ↦ U ≫ (G ≫ m)) hr).trans (by simp only [Category.assoc]))
    _ = (U ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationInitialBaseIso r s y).inv) ≫
        eqToHom (congrArg (fun a ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace a y) (he).symm) :=
      congrArg (fun m ↦ (U ≫ m) ≫
        eqToHom (congrArg (fun a ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace a y) (he).symm))
          (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.nativeSpanLeftUniversalHomDiagramFamily_terminal hp p c hc dB dC y)
    _ = _ := by
      rw [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeUniversalNativeParameter_terminal]
      simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]
end

section
local notation "σ" => stdSimplex.σ (2 : Fin 3) ≫ SSet.yonedaEquiv.symm (SSet.Edge.CompStruct.simplex
  (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpanRightTriangle c hc f (i ≫ p) rfl dB
    g (j ≫ p) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconePushoutBoundary_eq hp p) dC))
local notation "v" => (stdSimplex.δ (0 : Fin 2) ≫ stdSimplex.δ (0 : Fin 3)) ≫
  stdSimplex.δ (0 : Fin 4)
local notation "ht" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.nativeSpanRightHomDiagram_tip hp p c hc dB dC
local notation "G" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.nativeSpanRightUniversalHomDiagramFamily hp p c hc dB dC y

/-- 同じ右の native 図式の終端を、元の指定余錐の点図式表示へ揃える。 -/
lemma specifiedCoconeRightUniversalNative_tip : v ≫ σ = _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeVertexDiagram d :=
  (ht).trans (he).symm

/-- 元の指定余錐の全 Hom パラメータで表示した、同じ右の native 普遍全族。 -/
def specifiedCoconeRightUniversalNativeFamily :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomLeft (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone.vertex d) y ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace σ y := U ≫ G

/-- 共通パラメータでの native 普遍全族の終端は、元の指定余錐の同じ全 Hom の係数。 -/
lemma specifiedCoconeRightUniversalNativeFamily_terminal :
    specifiedCoconeRightUniversalNativeFamily hp p c hc dB dC y ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.normalizedCoconeRestrictionFiber σ v
          (specifiedCoconeRightUniversalNative_tip hp p c hc dB dC) y =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationInitialBaseIso q d y).inv := by
  have hr := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.normalizedCoconeRestrictionFiber_targetEq σ v
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeVertexDiagram s) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeVertexDiagram d) ht
    (specifiedCoconeRightUniversalNative_tip hp p c hc dB dC) (he).symm y
  calc
    _ = (U ≫ (G ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.normalizedCoconeRestrictionFiber σ v ht y)) ≫
        eqToHom (congrArg (fun a ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace a y) (he).symm) := by
      exact (Category.assoc U G (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.normalizedCoconeRestrictionFiber σ v
        (specifiedCoconeRightUniversalNative_tip hp p c hc dB dC) y)).trans
          ((congrArg (fun m ↦ U ≫ (G ≫ m)) hr).trans (by simp only [Category.assoc]))
    _ = (U ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationInitialBaseIso r s y).inv) ≫
        eqToHom (congrArg (fun a ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace a y) (he).symm) :=
      congrArg (fun m ↦ (U ≫ m) ≫
        eqToHom (congrArg (fun a ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace a y) (he).symm))
          (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.nativeSpanRightUniversalHomDiagramFamily_terminal hp p c hc dB dC y)
    _ = _ := by
      rw [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeUniversalNativeParameter_terminal]
      simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]
end

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
