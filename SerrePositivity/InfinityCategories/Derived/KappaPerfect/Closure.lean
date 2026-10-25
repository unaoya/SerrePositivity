module
public import SerrePositivity.KST.NonConnective.DGKappaPerfectInput
public import SerrePositivity.InfinityCategories.Derived.DGPretriangulatedModuleValuedCommonExact
public import SerrePositivity.InfinityCategories.Derived.DGModuleVertexShift
public import SerrePositivity.InfinityCategories.Stable.StableHoGeneration
public import SerrePositivity.InfinityCategories.Stable.ExactFunctorTriangulated

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
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
open SerrePositivity.KST.NonConnective
open scoped Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {κ : Cardinal.{u}} (I : DGKappaConeInput R D κ)

/-- 同じ cone の元の全 dg 加群への忘却。 -/
def dgKappaPerfectUnderlying : DGFunctor R (DGKappaCone R D I) (RightModule R D) :=
  (dgFullSubcategoryInclusion R (ModuleCategory R D) I.objects).comp (dgConeModuleForget R D)

/-- 小さい前三角始域からの実加群値関手の完全性。 -/
lemma dgKappaPerfectUnderlying_isExactFunctor :
    IsExactFunctor (dgNerve.map (dgKappaPerfectUnderlying R D I)) := by
  have h := dgPretriangulatedModuleValuedFunctorCommon_isExactFunctor.{u, max (u+1) v, v, 0}
    R (DGKappaCone R D I) D (dgKappaPerfectUnderlying R D I)
  exact isExactFunctor_of_ulift (dgNerve.map (dgKappaPerfectUnderlying R D I)) h

/-- 安定閉包の同じ対象条件は元の perfect 条件と一致する。 -/
lemma dgKappaPerfect_stableClosure_iff (M : DGKappaCone R D I) :
    dgStableClosureProperty R (DGKappaCone R D I) (dgKappaConePerfectObjects R D I) M ↔
      dgKappaConePerfectObjects R D I M := by
  constructor
  · intro hM
    let := dgNerve_isStable_of_pretriangulated R (DGKappaCone R D I)
    let := dgKappaPerfectUnderlying_isExactFunctor R D I
    let P := (modulePerfect R D).inverseImage (moduleHomotopyToDerivedClosed R D)
    let Q := (dgModuleHoProperty R D P).inverseImage
      (hoFunctor.map (dgNerve.map (dgKappaPerfectUnderlying R D I))).toFunctor
    have hle : stableHoClosure (Simplex.vertex '' dgKappaConePerfectObjects R D I) ≤ Q := by
      apply (stableHoClosure_le_iff _ Q).mpr
      rintro _ ⟨N, hN, rfl⟩
      change modulePerfect R D ((moduleHomotopyToDerivedClosed R D).obj
        ((moduleToHomotopy R D).obj N.val))
      exact (modulePerfect R D).prop_of_iso
        ((moduleToHomotopyDerivedIso R D).app N.val).symm hN
    have h := hle (SSet.HomotopyCategory.mk (Simplex.vertex M)) hM
    change modulePerfect R D ((moduleHomotopyToDerivedClosed R D).obj
      ((moduleToHomotopy R D).obj M.val)) at h
    exact (modulePerfect R D).prop_of_iso ((moduleToHomotopyDerivedIso R D).app M.val) h
  · intro hM
    exact StableVertexClosure.of_mem ⟨M, hM, rfl⟩

end SerrePositivity.InfinityCategories
