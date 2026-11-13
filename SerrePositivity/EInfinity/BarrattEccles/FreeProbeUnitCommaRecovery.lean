module

public import SerrePositivity.EInfinity.BarrattEccles.FreeProbeUnitStandardFamily

/-!
概要：実自由単位の comma 候補から、同じ単位の円柱と射の類を回収する。
方針：零単体の Yoneda 表示を元の fiber curry に戻し、既存の往復公式を使う。
規約：g1 の標準単位と候補自身を保持し、大域自由関手は入力にしない。
使われ方：同じ候補の実始対象性の局所判定への入力。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial
variable (A : Type u) [CommRing A]

lemma derivedFreeProbeUnitIntervalMap_isSimplicialHomotopyEquivalence
    (x : (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory A) _⦋0⦌) (y : (CAlg_R A) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (derivedFreeProbeUnitIntervalMap A x y) :=
  (derivedFreeProbeUnitIntervalMap_weak A x y).isSimplicialHomotopyEquivalence

lemma derivedFreeProbeUnitIntervalMap_isQCatEquivalence
    (x : (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory A) _⦋0⦌) (y : (CAlg_R A) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (derivedFreeProbeUnitIntervalMap A x y) :=
  (derivedFreeProbeUnitIntervalMap_isSimplicialHomotopyEquivalence A x y).isQCatEquivalence

lemma derivedFreeProbeUnitCommaVertex_homotopy_h
    (x : (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory A) _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiberHomotopy
      (SSet.const (derivedFreeProbeUnitCommaVertex A x) :
        Δ[0] ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiber (cAlgForgetDerived A) x)).h =
      (derivedFreeProbeUnitPointHomotopy A x Δ[0]).h := by
  have hc : (SSet.const (derivedFreeProbeUnitCommaVertex A x) :
      Δ[0] ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiber (cAlgForgetDerived A) x) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiberCurry (cAlgForgetDerived A) x
        (SSet.const (derivedFreeProbeVertex A x))
        (derivedFreeProbeUnitPointHomotopy A x Δ[0]) :=
    (SSet.yonedaEquiv_symm_zero _).symm.trans (Equiv.symm_apply_apply _ _)
  exact (congrArg (fun f : Δ[0] ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiber (cAlgForgetDerived A) x ↦
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiberHomotopy f).h) hc).trans (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiberCurry_homotopy _ _ _ _)

lemma derivedFreeProbeUnitCommaVertex_hom
    (x : (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory A) _⦋0⦌) : HEq
    (Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiberHomotopy
        (SSet.const (derivedFreeProbeUnitCommaVertex A x) :
          Δ[0] ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiber (cAlgForgetDerived A) x))))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorHomMap Δ[0] (derivedFreeProbeUnitHom A x)) := by
  exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomotopyHom_heq_of_raw_eq _ _
    (derivedFreeProbeUnitCommaVertex_homotopy_h A x)).trans
      (derivedFreeProbeUnitPointHomotopy_hom A x Δ[0])

end SerrePositivity.EInfinity.BarrattEccles
