module

public import SerrePositivity.InfinityCategories.F2.Compact.WeakUniverse
public import SerrePositivity.InfinityCategories.F2.LargeTotalCoconeUnit

/-!
概要：元の全空間余極限余錐の実際の fiber 写像は、大きい全 Kan 標的で弱同値。
方針：同じ小さい単位の宇宙持ち上げの弱同値性を、保存済みの全自然同型で移す。
規約：小さい Kan 標的だけの検査で代用せず、一段大きい全標的を扱う。
使われ方：指定した空間の宇宙変更に対する小さい余極限保存。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.F2.Compact
attribute [local instance] vertexFiber_kanComplex_of_leftFibration

/-- 元の小さい全空間の単位を大きい全空間から表示した同じ射は、全 Kan 標的で弱同値。 -/
lemma coherentLargeTotalUnit_isWeakHomotopyEquivalence {B : SSet.{u}}
    (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}) :
    IsWeakHomotopyEquivalence (coherentLargeTotalUnit F) := by
  have h := isPrecompositionEquivalence_of_iso (smallLeftUnstraighteningIso F).symm
  exact h.isWeakHomotopyEquivalence.comp
    (weakHomotopyEquivalence_ulift (coherentDiagramTotalUnit F)
      (coherentDiagramTotalUnit_isWeakHomotopyEquivalence F))

/-- 元の指定頂点の値への実際の全空間写像は、大きい宇宙でも弱ホモトピー同値。 -/
lemma coherentTotalCoconeFiberValue_isWeakHomotopyEquivalence {B : SSet.{u}}
    (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}) :
    IsWeakHomotopyEquivalence (coconeFiberValueMapAt (coherentDiagramTotalCocone F)
      (coherentDiagramTotalVertex F) (coherentDiagramTotalCocone_vertex F)) :=
  (weakHomotopyEquivalence_iff_of_functorIso (coherentLargeTotalCoconeUnitIso F)).mpr
    (coherentLargeTotalUnit_isWeakHomotopyEquivalence F)

/-- 元の全余極限余錐の実際の fiber 写像は、大きい全 Kan 標的への前合成で弱同値。 -/
lemma coherentTotalCoconeFiber_isWeakHomotopyEquivalence {B : SSet.{u}}
    (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}) :
    IsWeakHomotopyEquivalence (coconeFiberMap (coherentDiagramTotalCocone F)) := by
  let h := coherentDiagramTotalCocone_vertex F
  let r := eqToHom (congrArg (vertexFiber pointedSpaceProjection) h) ≫
    (pointedSpaceFiberValueEquivalence (coherentDiagramTotalVertex F)).hom
  have hr : IsWeakHomotopyEquivalence r := by
    have h₀ := isPrecompositionEquivalence_of_iso
      (eqToIso (congrArg (vertexFiber pointedSpaceProjection) h))
    have h₁ := (pointedSpaceFiberValueEquivalence (coherentDiagramTotalVertex F)).isQCatEquivalence
    exact h₀.isWeakHomotopyEquivalence.comp h₁.isWeakHomotopyEquivalence
  exact hr.cancel_right (coherentTotalCoconeFiberValue_isWeakHomotopyEquivalence F)

end SerrePositivity.InfinityCategories.F2.Compact
