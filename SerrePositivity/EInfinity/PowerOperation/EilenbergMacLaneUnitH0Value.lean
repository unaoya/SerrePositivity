module

public import SerrePositivity.EInfinity.PowerOperation.EilenbergMacLaneUnitDeshift
public import SerrePositivity.EInfinity.PowerOperation.EilenbergMacLaneUnitVertexClass
public import SerrePositivity.EInfinity.PowerOperation.UnitPrecompositionHomology

/-!
# 指定構造射の H⁰ の単位での値と標準基点での Ω 条件

DAG XIII §2.2 の零次数の Ω 比較。固定した基本円・実シフト自己同型・
零 loop の逆元を同じ実単位自己同型へ運び、その可逆性で全次数を閉じる。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.PowerOperation
open CategoryTheory HomologicalComplex MonoidalCategory
open SerrePositivity.DifferentialGraded
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups
open SerrePositivity.KST.Spectra (pointedGroupMap pointedHomotopyMap)
variable (A : Type u) [CommRing A]

/-- 固定した円の指定自己同型による後合成の類は、元の基本類の誘導像。 -/
lemma gammaUnitCircle_shift_class :
    KanHomotopyGroup.mk (KST.Spectra.SphereSimplex.equiv
      (gammaPointed A ((𝟙_ (Complex A))⟦(1 : ℤ)⟧)) 1
      (unitCircle A ≫ (gammaPointedFunctor A).map (unitShiftAutomorphism A).hom)) =
      pointedGroupMap 0 ((gammaPointedFunctor A).map (unitShiftAutomorphism A).hom)
        (unitCircleClass A) := by
  rw [KST.Spectra.SphereSimplex.equiv_comp, ← KanHomotopyGroup.map_mk]
  exact congrArg
    (pointedGroupMap 0 ((gammaPointedFunctor A).map (unitShiftAutomorphism A).hom))
    (unitCircle_class A)

/-- 指定 H⁰ 写像の単位での値は、符号を保持した実単位自己同型の類。 -/
lemma gammaSuspensionH0Map_unit :
    gammaSuspensionH0Map A (𝟙_ (Complex A))
      (_root_.SerrePositivity.HomologyZero.unitClass (𝟙_ (Complex A)) (𝟙 _)) =
      _root_.SerrePositivity.HomologyZero.unitClass (𝟙_ (Complex A)) (signedUnitDeshiftAutomorphism A).hom := by
  dsimp only [gammaSuspensionH0Map, Function.comp_apply]
  rw [gammaBasedPiZeroCohomologyEquiv_symm_unit, gammaUnitVertexClass_map_adjoint]
  change (((homologyFunctor (ModuleCat A) (.up ℤ) 0).shiftIso
    (1 : ℤ) (-1 : ℤ) (0 : ℤ) (by decide)).app (𝟙_ (Complex A))).hom.hom
      (Multiplicative.toAdd (gammaPiCohomologyEquiv A ((𝟙_ (Complex A))⟦(1 : ℤ)⟧) 0
        (KST.Spectra.loopZeroHomotopyEquiv (gammaPointed A ((𝟙_ (Complex A))⟦(1 : ℤ)⟧))
          (KanHomotopy.mk 0 _)))) = _
  rw [gammaAdjointSuspension_unit_loop_class, gammaUnitCircle_shift_class, map_inv]
  change (((homologyFunctor (ModuleCat A) (.up ℤ) 0).shiftIso
    (1 : ℤ) (-1 : ℤ) (0 : ℤ) (by decide)).app (𝟙_ (Complex A))).hom.hom
      (-Multiplicative.toAdd (gammaPiCohomologyEquiv A ((𝟙_ (Complex A))⟦(1 : ℤ)⟧) 0
        (pointedGroupMap 0 ((gammaPointedFunctor A).map (unitShiftAutomorphism A).hom)
          (unitCircleClass A)))) =
      _root_.SerrePositivity.HomologyZero.unitClass (𝟙_ (Complex A)) (-(unitDeshiftAutomorphism A).hom)
  rw [map_neg, map_neg]
  exact congrArg (fun x : (𝟙_ (Complex A)).homology 0 => -x)
    (gammaUnitShiftAction_cohomology A)

/-- 指定随伴構造射は標準の零基点で全自然数次数のホモトピー類に全単射。 -/
lemma gammaAdjointSuspension_bijective_at_basepoint (M : Complex A) (n : ℕ) :
    Function.Bijective (pointedHomotopyMap n ((gammaAdjointSuspension A).app M)) := by
  apply gammaAdjointSuspension_bijective_of_zero A _ M n
  intro N
  apply (gammaSuspensionH0Map_bijective_iff A N).mp
  exact homologyZeroNatural_bijective_of_unit_iso (gammaSuspensionH0Map A)
    (fun f x => gammaSuspensionH0Map_naturality A f x)
    (signedUnitDeshiftAutomorphism A) (gammaSuspensionH0Map_unit A) N

end SerrePositivity.EInfinity.PowerOperation
