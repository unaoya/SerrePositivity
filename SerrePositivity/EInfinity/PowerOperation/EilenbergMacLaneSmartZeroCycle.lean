module

public import SerrePositivity.EInfinity.PowerOperation.EilenbergMacLaneGammaZeroRepresentative
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.ExtendedTruncationZeroInclusion

/-!
# smart 切断の零次の元を元の閉元とホモロジー類へ戻す

DAG XIII §2.2 の零次数の Ω 比較への前段。同じ延長同型と切断包含を保持する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.PowerOperation
open CategoryTheory HomologicalComplex
open SerrePositivity.DifferentialGraded _root_.SerrePositivity.ComplexLimits
variable (A : Type u) [CommRing A]

/-- 非負鎖複体の類写像は、実 cycles の零次数同型によっても計算できる。 -/
lemma chainZeroClass_eq_cycles (K : ChainComplex (ModuleCat A) ℕ) :
    chainZeroClass K = (ChainComplex.cycles₀Iso K).inv ≫ K.homologyπ 0 := by
  apply (cancel_mono (K.homologyι 0)).mp
  simp only [chainZeroClass, Category.assoc, HomologicalComplex.isoHomologyι_inv_hom_id,
    Category.comp_id, homology_π_ι, ChainComplex.cycles₀Iso, iCyclesIso_inv_hom_id_assoc]

/-- 元の smart 切断の閉元を、同じ延長の実射で元の cycles に送る。 -/
def smartTruncationZeroCycleMap (M : Complex A) :
    (M.truncLE' (ComplexShape.embeddingUpIntLE 0)).X 0 ⟶ M.cycles 0 :=
  (ChainComplex.cycles₀Iso (M.truncLE' (ComplexShape.embeddingUpIntLE 0))).inv ≫
    ((M.truncLE' (ComplexShape.embeddingUpIntLE 0)).extendCyclesIso
      (ComplexShape.embeddingUpIntLE 0) (j := 0) (j' := 0) (by simp)).inv ≫
    cyclesMap (M.truncLEIso (ComplexShape.embeddingUpIntLE 0)).inv 0 ≫
      cyclesMap (ιTruncLE M (ComplexShape.embeddingUpIntLE 0)) 0

/-- cycles の包含後には、元の指定された零次数包含そのものになる。 -/
@[reassoc]
lemma smartTruncationZeroCycleMap_iCycles (M : Complex A) :
    smartTruncationZeroCycleMap A M ≫ M.iCycles 0 =
      _root_.SerrePositivity.ComplexLimits.truncationExtendedZeroInclusion A (ComplexShape.embeddingUpIntLE 0) rfl (by simp) M := by
  simp only [smartTruncationZeroCycleMap, Category.assoc, cyclesMap_i, cyclesMap_i_assoc,
    extendCyclesIso_inv_iCycles_assoc, ChainComplex.cycles₀Iso, iCyclesIso_inv_hom_id_assoc]
  rfl

/-- 同じ閉元の写像を実ホモロジー射で写すと、指定 smart 切断比較になる。 -/
lemma smartTruncationZeroCycleMap_homologyπ (M : Complex A) :
    smartTruncationZeroCycleMap A M ≫ M.homologyπ 0 =
      chainZeroClass (M.truncLE' (ComplexShape.embeddingUpIntLE 0)) ≫
        (smartTruncationHomologyIso A M 0).hom := by
  rw [chainZeroClass_eq_cycles A]
  change _ = (ChainComplex.cycles₀Iso (M.truncLE' (ComplexShape.embeddingUpIntLE 0))).inv ≫
    (M.truncLE' (ComplexShape.embeddingUpIntLE 0)).homologyπ 0 ≫
      ((M.truncLE' (ComplexShape.embeddingUpIntLE 0)).extendHomologyIso
        (ComplexShape.embeddingUpIntLE 0) (j := 0) (j' := 0) (by simp)).inv ≫
      homologyMap (M.truncLEIso (ComplexShape.embeddingUpIntLE 0)).inv 0 ≫
        homologyMap (ιTruncLE M (ComplexShape.embeddingUpIntLE 0)) 0
  simp only [smartTruncationZeroCycleMap, Category.assoc,
    homologyπ_extendHomologyIso_inv_assoc, homologyπ_naturality, homologyπ_naturality_assoc]

end SerrePositivity.EInfinity.PowerOperation
