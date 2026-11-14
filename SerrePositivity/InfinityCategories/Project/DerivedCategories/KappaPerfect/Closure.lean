module
public import SerrePositivity.KST.NonConnective.DGKappaPerfectInput
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Triangles.DGPretriangulatedModuleValuedCommonExact
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Actions.DGModuleVertexShift
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.StableHoGeneration
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExactFunctorTriangulated

/-!
概要：同じ κ-cone の perfect 対象条件は native 安定閉包で変わらない。
方針：元の加群値 dg 関手の完全性と、主導来圏の perfect 三角的条件を使う。
規約：κ-compact 性・全被覆は使用しない。使われ方：D-8 e の実 Perf への逆向き比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaPerfect
open CategoryTheory DifferentialGraded SSet
open _root_.SerrePositivity.KST.NonConnective
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]
  {κ : Cardinal.{u}} (I : DGKappaConeInput R D κ)

/-- 同じ cone の元の全 dg 加群への忘却。 -/
def dgKappaPerfectUnderlying : _root_.SerrePositivity.DifferentialGraded.DGFunctor R (DGKappaCone R D I) (_root_.SerrePositivity.DifferentialGraded.RightModule R D) :=
  (_root_.SerrePositivity.DifferentialGraded.dgFullSubcategoryInclusion R (_root_.SerrePositivity.DifferentialGraded.ModuleCategory R D) I.objects).comp (dgConeModuleForget R D)

/-- 小さい前三角始域からの実加群値関手の完全性。 -/
lemma dgKappaPerfectUnderlying_isExactFunctor :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgKappaPerfectUnderlying R D I)) := by
  have h := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPretriangulatedModuleValuedFunctorCommon_isExactFunctor.{u, max (u+1) v, v, 0}
    R (DGKappaCone R D I) D (dgKappaPerfectUnderlying R D I)
  exact _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.isExactFunctor_of_ulift (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgKappaPerfectUnderlying R D I)) h

/-- 安定閉包の同じ対象条件は元の perfect 条件と一致する。 -/
lemma dgKappaPerfect_stableClosure_iff (M : DGKappaCone R D I) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStableClosureProperty R (DGKappaCone R D I) (dgKappaConePerfectObjects R D I) M ↔
      dgKappaConePerfectObjects R D I M := by
  constructor
  · intro hM
    let := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Pretriangulated.dgNerve_isStable_of_pretriangulated R (DGKappaCone R D I)
    let := dgKappaPerfectUnderlying_isExactFunctor R D I
    let P := (_root_.SerrePositivity.DifferentialGraded.modulePerfect R D).inverseImage (_root_.SerrePositivity.DifferentialGraded.moduleHomotopyToDerivedClosed R D)
    let Q := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleHoProperty R D P).inverseImage
      (hoFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgKappaPerfectUnderlying R D I))).toFunctor
    have hle : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stableHoClosure (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex '' dgKappaConePerfectObjects R D I) ≤ Q := by
      apply (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stableHoClosure_le_iff _ Q).mpr
      rintro _ ⟨N, hN, rfl⟩
      change _root_.SerrePositivity.DifferentialGraded.modulePerfect R D ((_root_.SerrePositivity.DifferentialGraded.moduleHomotopyToDerivedClosed R D).obj
        ((_root_.SerrePositivity.DifferentialGraded.moduleToHomotopy R D).obj N.val))
      exact (_root_.SerrePositivity.DifferentialGraded.modulePerfect R D).prop_of_iso
        ((_root_.SerrePositivity.DifferentialGraded.moduleToHomotopyDerivedIso R D).app N.val).symm hN
    have h := hle (SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex M)) hM
    change _root_.SerrePositivity.DifferentialGraded.modulePerfect R D ((_root_.SerrePositivity.DifferentialGraded.moduleHomotopyToDerivedClosed R D).obj
      ((_root_.SerrePositivity.DifferentialGraded.moduleToHomotopy R D).obj M.val)) at h
    exact (_root_.SerrePositivity.DifferentialGraded.modulePerfect R D).prop_of_iso ((_root_.SerrePositivity.DifferentialGraded.moduleToHomotopyDerivedIso R D).app M.val) h
  · intro hM
    exact _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.StableVertexClosure.of_mem ⟨M, hM, rfl⟩

end SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaPerfect
