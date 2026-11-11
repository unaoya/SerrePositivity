module
public import SerrePositivity.KST.Fibration.VerdierLowerCanonicalShortFaces

/-!
概要：正規化下側の両有限端点を元の指定二胞体へ戻す三つの照合条件を保持する。
方針：同じ二短辺・全 native Hom と元の下側変形の両端を照合する。
規約：有限二胞体の外延性自体は F1 正本に残し、厳密切断を使わない。
使われ方：K-6 c4 の四つの有限端点のうち下側二端の実入力。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration
private theorem lowerFiniteNative_heq_of_eq (s t : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} _⦋2⦌) (h : s = t) :
    HEq (s.map ⟨ULift.up 0⟩ ⟨ULift.up 2⟩) (t.map ⟨ULift.up 0⟩ ⟨ULift.up 2⟩) := by
  cases h
  rfl

variable (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u})

/-- 概要：元の下側全変形の始端は指定下側二胞体そのもの。
方針：同じ実三角柱の始端を回収する。
規約：全二胞体の厳密等式。使われ方：正規化始端の比較先。 -/
theorem verdierLowerDeformationFamily_first :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.familyAtVertex (verdierFullSLowerDeformation d).h (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) =
      SSet.yonedaEquiv.symm (verdierFullSLowerSimplex d) :=
  (verdierFullSLowerDeformation d).h₀

/-- 概要：元の下側全変形の終端は同じ最大 path 二胞体。
方針：同じ実三角柱の終端を回収する。
規約：全二胞体の厳密等式。使われ方：同じ実商核への有限終端照合。 -/
theorem verdierLowerDeformationFamily_last :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.familyAtVertex (verdierFullSLowerDeformation d).h (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) =
      SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentSimplexMaximalization (verdierFullSLowerSimplex d)) :=
  (verdierFullSLowerDeformation d).h₁

variable (ℓ : (verdierLowerCanonicalLongSpace d) _⦋0⦌)

/-- 概要：正規化下側の各有限パラメータで第一面は元の同じ面。
方針：同じ全短辺を Yoneda の面座標へ戻す。
規約：厳密な面等号。使われ方：F1 外延性の第一面入力。 -/
theorem verdierLowerCanonicalFamily_delta_two (k : (Δ[1] : SSet.{u + 1}) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.δ (2 : Fin 3) (SSet.yonedaEquiv
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.familyAtVertex (verdierLowerCanonicalFamily d ℓ) k)) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.δ (2 : Fin 3) (SSet.yonedaEquiv
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.familyAtVertex (verdierFullSLowerDeformation d).h k)) := by
  apply SSet.yonedaEquiv.symm.injective
  simpa only [← stdSimplex.δ_comp_yonedaEquiv_symm, Equiv.symm_apply_apply] using
    verdierLowerCanonicalFamily_vertex_first d ℓ k

/-- 概要：正規化下側の各有限パラメータで第二面は元の同じ面。
方針：同じ全短辺を Yoneda の面座標へ戻す。
規約：厳密な面等号。使われ方：F1 外延性の第二面入力。 -/
theorem verdierLowerCanonicalFamily_delta_zero (k : (Δ[1] : SSet.{u + 1}) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.δ (0 : Fin 3) (SSet.yonedaEquiv
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.familyAtVertex (verdierLowerCanonicalFamily d ℓ) k)) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.δ (0 : Fin 3) (SSet.yonedaEquiv
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.familyAtVertex (verdierFullSLowerDeformation d).h k)) := by
  apply SSet.yonedaEquiv.symm.injective
  simpa only [← stdSimplex.δ_comp_yonedaEquiv_symm, Equiv.symm_apply_apply] using
    verdierLowerCanonicalFamily_vertex_last d ℓ k

/-- 概要：正規化始端の第一面は元の指定下側二胞体の第一面。
方針：同じ面回収に元の実始端を代入する。
規約：二胞体の同定を先取りしない。使われ方：有限始端の第一条件。 -/
theorem verdierLowerCanonicalFamily_first_delta_two :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.δ (2 : Fin 3) (SSet.yonedaEquiv
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.familyAtVertex (verdierLowerCanonicalFamily d ℓ) (stdSimplex.obj₀Equiv.symm (0 : Fin 2)))) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.δ (2 : Fin 3) (verdierFullSLowerSimplex d) := by
  have h := verdierLowerCanonicalFamily_delta_two d ℓ (stdSimplex.obj₀Equiv.symm (0 : Fin 2))
  have he := (congrArg SSet.yonedaEquiv (verdierLowerDeformationFamily_first d)).trans
    ((SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})).apply_symm_apply (verdierFullSLowerSimplex d))
  exact h.trans (congrArg (fun z : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} _⦋2⦌ => _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.δ (2 : Fin 3) z) he)

/-- 概要：正規化始端の第二面は元の指定下側二胞体の第二面。
方針：同じ面回収に元の実始端を代入する。
規約：二胞体の同定を先取りしない。使われ方：有限始端の第二条件。 -/
theorem verdierLowerCanonicalFamily_first_delta_zero :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.δ (0 : Fin 3) (SSet.yonedaEquiv
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.familyAtVertex (verdierLowerCanonicalFamily d ℓ) (stdSimplex.obj₀Equiv.symm (0 : Fin 2)))) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.δ (0 : Fin 3) (verdierFullSLowerSimplex d) := by
  have h := verdierLowerCanonicalFamily_delta_zero d ℓ (stdSimplex.obj₀Equiv.symm (0 : Fin 2))
  have he := (congrArg SSet.yonedaEquiv (verdierLowerDeformationFamily_first d)).trans
    ((SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})).apply_symm_apply (verdierFullSLowerSimplex d))
  exact h.trans (congrArg (fun z : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} _⦋2⦌ => _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.δ (0 : Fin 3) z) he)

/-- 概要：正規化終端の第一面は元の最大 path 二胞体の第一面。
方針：同じ面回収に元の実終端を代入する。
規約：標準二胞体を保持。使われ方：有限終端の第一条件。 -/
theorem verdierLowerCanonicalFamily_last_delta_two :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.δ (2 : Fin 3) (SSet.yonedaEquiv
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.familyAtVertex (verdierLowerCanonicalFamily d ℓ) (stdSimplex.obj₀Equiv.symm (1 : Fin 2)))) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.δ (2 : Fin 3) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentSimplexMaximalization (verdierFullSLowerSimplex d)) := by
  have h := verdierLowerCanonicalFamily_delta_two d ℓ (stdSimplex.obj₀Equiv.symm (1 : Fin 2))
  have he := (congrArg SSet.yonedaEquiv (verdierLowerDeformationFamily_last d)).trans
    ((SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})).apply_symm_apply (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentSimplexMaximalization (verdierFullSLowerSimplex d)))
  exact h.trans (congrArg (fun z : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} _⦋2⦌ => _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.δ (2 : Fin 3) z) he)

/-- 概要：正規化終端の第二面は元の最大 path 二胞体の第二面。
方針：同じ面回収に元の実終端を代入する。
規約：標準二胞体を保持。使われ方：有限終端の第二条件。 -/
theorem verdierLowerCanonicalFamily_last_delta_zero :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.δ (0 : Fin 3) (SSet.yonedaEquiv
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.familyAtVertex (verdierLowerCanonicalFamily d ℓ) (stdSimplex.obj₀Equiv.symm (1 : Fin 2)))) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.δ (0 : Fin 3) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentSimplexMaximalization (verdierFullSLowerSimplex d)) := by
  have h := verdierLowerCanonicalFamily_delta_zero d ℓ (stdSimplex.obj₀Equiv.symm (1 : Fin 2))
  have he := (congrArg SSet.yonedaEquiv (verdierLowerDeformationFamily_last d)).trans
    ((SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})).apply_symm_apply (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentSimplexMaximalization (verdierFullSLowerSimplex d)))
  exact h.trans (congrArg (fun z : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} _⦋2⦌ => _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.δ (0 : Fin 3) z) he)

variable
  (L : (Δ[1] : SSet.{u + 1}) ⟶ (ihom ((SSet.uliftFunctor.{u + 1, u}).obj
    (nerve _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TriangleNativePath.{u}))).obj (verdierLowerNativeLongHomTarget d))
  (hfull : L ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (ULift.up (ComposableArrows.mk₀ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleFullPath.{u})) =
    verdierLowerReconstructionCompositeFamily d Δ[1])
  (hL : VerdierLowerNativeReadoutRecovery d L)
include hL

/-- 概要：正規化始端の全 native Hom は元の指定下側二胞体の全 native Hom。
方針：同じ実読出し回収と元の実始端の全等号を合成する。
規約：直接端だけへ弱めない。使われ方：下側有限始端の第三条件。 -/
theorem verdierLowerCanonicalReadout_first_native :
    HEq ((SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.familyAtVertex
      (verdierLowerCanonicalFamily d (verdierLowerCanonicalReadout d L hfull))
        (stdSimplex.obj₀Equiv.symm (0 : Fin 2)))).map ⟨ULift.up 0⟩ ⟨ULift.up 2⟩)
      ((verdierFullSLowerSimplex d).map ⟨ULift.up 0⟩ ⟨ULift.up 2⟩) := by
  have he := (congrArg SSet.yonedaEquiv (verdierLowerDeformationFamily_first d)).trans
    (Equiv.apply_symm_apply SSet.yonedaEquiv (verdierFullSLowerSimplex d))
  exact (verdierLowerCanonicalReadout_vertex_native d L hfull hL
    (stdSimplex.obj₀Equiv.symm (0 : Fin 2))).trans (lowerFiniteNative_heq_of_eq _ _ he)

/-- 概要：正規化終端の全 native Hom は元の最大 path 二胞体の全 native Hom。
方針：同じ実読出し回収と元の実終端の全等号を合成する。
規約：標準二胞体の全 Hom を保持。使われ方：下側有限終端の第三条件。 -/
theorem verdierLowerCanonicalReadout_last_native :
    HEq ((SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.familyAtVertex
      (verdierLowerCanonicalFamily d (verdierLowerCanonicalReadout d L hfull))
        (stdSimplex.obj₀Equiv.symm (1 : Fin 2)))).map ⟨ULift.up 0⟩ ⟨ULift.up 2⟩)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentSimplexMaximalization (verdierFullSLowerSimplex d)).map
        ⟨ULift.up 0⟩ ⟨ULift.up 2⟩) := by
  have he := (congrArg SSet.yonedaEquiv (verdierLowerDeformationFamily_last d)).trans
    (Equiv.apply_symm_apply SSet.yonedaEquiv
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentSimplexMaximalization (verdierFullSLowerSimplex d)))
  exact (verdierLowerCanonicalReadout_vertex_native d L hfull hL
    (stdSimplex.obj₀Equiv.symm (1 : Fin 2))).trans (lowerFiniteNative_heq_of_eq _ _ he)

end SerrePositivity.KST.Fibration
