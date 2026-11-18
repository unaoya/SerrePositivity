module

public import SerrePositivity.EInfinity.PowerOperation.EilenbergMacLaneSmartZeroCycle
public import SerrePositivity.EInfinity.PowerOperation.CochainZeroCycleClass
public import SerrePositivity.EInfinity.PowerOperation.EilenbergMacLaneUnitCoefficient

/-!
# 指定 AW 単位の Γ の成分は元の H⁰ の単位類である

DAG XIII §2.2 の零次数の Ω 比較への前段。同じ正規化余単位と閉元の包含を使い、
指定単位の係数一の計算を実ホモロジーの類へ運ぶ。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.PowerOperation
open CategoryTheory HomologicalComplex MonoidalCategory
open scoped Simplicial
open SerrePositivity.DifferentialGraded _root_.SerrePositivity.ComplexLimits
variable (A : Type u) [CommRing A]

/-- 同じ π₀/H⁰ 比較の零単体の値は、同じ閉元の実ホモロジー類である。 -/
lemma gammaPiZeroCohomologyEquiv_mk_cycle (M : Complex A)
    (x : (gammaModule A M).obj (Opposite.op ⦋0⦌)) :
    gammaPiZeroCohomologyEquiv A M (SSet.π₀.mk x) =
      (M.homologyπ 0).hom ((smartTruncationZeroCycleMap A M).hom
        ((_root_.SerrePositivity.ComplexLimits.gammaDegreeZeroIso (M.truncLE' (ComplexShape.embeddingUpIntLE 0))).hom.hom x)) := by
  change (smartTruncationHomologyIso A M 0).hom.hom
    (gammaPiZeroTruncationEquiv A M (SSet.π₀.mk x)) = _
  rw [gammaPiZeroTruncationEquiv_mk]
  exact congrArg (fun k => k.hom
    ((_root_.SerrePositivity.ComplexLimits.gammaDegreeZeroIso (M.truncLE' (ComplexShape.embeddingUpIntLE 0))).hom.hom x))
    (smartTruncationZeroCycleMap_homologyπ A M).symm

/-- 指定単位の閉元を実 cycles で計算する。 -/
lemma gammaUnitSimplex_zero_cycle :
    (smartTruncationZeroCycleMap A (𝟙_ (Complex A))).hom
      ((_root_.SerrePositivity.ComplexLimits.gammaDegreeZeroIso ((𝟙_ (Complex A)).truncLE'
        (ComplexShape.embeddingUpIntLE 0))).hom.hom (gammaUnitSimplex A ⦋0⦌)) =
      (zeroCyclesActualIso (𝟙_ (Complex A))).hom (cycleFromUnit (𝟙_ (Complex A)) (𝟙 _)) := by
  let I := 𝟙_ (Complex A)
  let z := (_root_.SerrePositivity.ComplexLimits.gammaDegreeZeroIso (I.truncLE' (ComplexShape.embeddingUpIntLE 0))).hom.hom
    (gammaUnitSimplex A ⦋0⦌)
  apply (ModuleCat.mono_iff_injective
    (I.iCycles 0 ≫ (singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat A))).hom)).mp inferInstance
  change (singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat A))).hom
    ((smartTruncationZeroCycleMap A I ≫ I.iCycles 0).hom z) = _
  rw [smartTruncationZeroCycleMap_iCycles]
  have h : (singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat A))).hom
      ((_root_.SerrePositivity.ComplexLimits.truncationExtendedZeroInclusion A (ComplexShape.embeddingUpIntLE 0) rfl
        (by simp) I).hom z) = (1 : A) := by
    simpa only [_root_.SerrePositivity.ComplexLimits.embeddingDownNat_eq_upIntLE_zero] using gammaUnitSimplex_zero_coefficient A
  rw [h]
  have hi := congrArg (fun k => k.hom (cycleFromUnit I (𝟙 I))) (zeroCyclesActualIso_i I)
  change (I.iCycles 0).hom ((zeroCyclesActualIso I).hom.hom (cycleFromUnit I (𝟙 I))) =
    (cycleFromUnit I (𝟙 I)).val at hi
  change (1 : A) = (singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat A))).hom
    ((I.iCycles 0).hom ((zeroCyclesActualIso I).hom.hom (cycleFromUnit I (𝟙 I))))
  rw [hi]
  exact ((singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat A))).inv_hom_id_apply (1 : A)).symm

/-- 同じ指定 π₀/H⁰ 比較は AW 単位の成分を元の単位類へ送る。 -/
lemma gammaPiZeroCohomologyEquiv_unit :
    gammaPiZeroCohomologyEquiv A (𝟙_ (Complex A)) (SSet.π₀.mk (gammaUnitSimplex A ⦋0⦌)) =
      _root_.SerrePositivity.HomologyZero.unitClass (𝟙_ (Complex A)) (𝟙 _) := by
  rw [gammaPiZeroCohomologyEquiv_mk_cycle, gammaUnitSimplex_zero_cycle]
  exact congrArg (fun k => k.hom (cycleFromUnit (𝟙_ (Complex A)) (𝟙 _)))
    (zeroCyclesActualIso_homologyπ (𝟙_ (Complex A)))

end SerrePositivity.EInfinity.PowerOperation
