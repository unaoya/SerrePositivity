module

public import SerrePositivity.EInfinity.BarrattEccles.FreeProbeDerivedUnitVertex
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.UnitCommaArrowFamilies
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.FunctorHomotopyRawTransport

/-!
# 同じ U の各 comma fiber の実自由単位候補

概要：元の導来自由単位から、各固定始域の comma fiber の実頂点を作る。
方針：同じ単位の定値族の二胞体をホモトピーにし、元の fiber curry を適用する。
規約：単位の射の類と実自由 probe の標的頂点を保持する。始対象性は後続。
使われ方：全 coherent ∞ 随伴の局所存在判定。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory SSet
open SerrePositivity.InfinityCategories DifferentialGraded
open scoped Simplicial
variable (A : Type u) [CommRing A]

def derivedFreeProbeUnitPointHomotopy (x : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityCategory A) _⦋0⦌)
    (T : SSet.{u + 1}) :
    SSet.Homotopy (SSet.const x : T ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityCategory A)
      ((SSet.const (derivedFreeProbeVertex A x) : T ⟶ CAlg_R A) ≫ cAlgForgetDerived A) :=
  _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stableHomotopyRetarget
    (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomHomotopy (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorHomMap T (derivedFreeProbeUnitHom A x))) rfl
      (SSet.const_comp _ _).symm

lemma derivedFreeProbeUnitPointHomotopy_hom (x : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityCategory A) _⦋0⦌)
    (T : SSet.{u + 1}) : HEq
    (Truncated.HomotopyCategory.homMk
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (derivedFreeProbeUnitPointHomotopy A x T)))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorHomMap T (derivedFreeProbeUnitHom A x)) := by
  have h := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomotopyHom_heq_of_raw_eq (derivedFreeProbeUnitPointHomotopy A x T)
    (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomHomotopy (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorHomMap T (derivedFreeProbeUnitHom A x))) rfl
  exact h.trans (heq_of_eq (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomHomotopy_hom _))

def derivedFreeProbeUnitCommaVertex (x : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityCategory A) _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiber (cAlgForgetDerived A) x) _⦋0⦌ :=
  SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiberCurry (cAlgForgetDerived A) x
    (SSet.const (derivedFreeProbeVertex A x) : Δ[0] ⟶ CAlg_R A)
      (derivedFreeProbeUnitPointHomotopy A x Δ[0]))

lemma derivedFreeProbeUnitCommaVertex_target (x : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityCategory A) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiberTargetVertex (cAlgForgetDerived A) x (derivedFreeProbeUnitCommaVertex A x) =
      derivedFreeProbeVertex A x := by
  change SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiberTarget
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiberCurry (cAlgForgetDerived A) x
      (SSet.const (derivedFreeProbeVertex A x) : Δ[0] ⟶ CAlg_R A)
        (derivedFreeProbeUnitPointHomotopy A x Δ[0]))) = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiberCurry_target]
  rfl

end SerrePositivity.EInfinity.BarrattEccles
