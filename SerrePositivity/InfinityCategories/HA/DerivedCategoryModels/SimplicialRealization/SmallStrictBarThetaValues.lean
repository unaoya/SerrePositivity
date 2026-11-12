module

public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization.SmallStrictBarSignedColumns
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization.SmallStrictBarBoundaryFaces
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization.SmallStrictBarColumns
import all SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization.SmallStrictBarTotalColumns

/-!
# 同じ theta の列の比較による後合成

## 概要
既存の theta の各列を比較へ送ると、シフト前の標準列の微分に一致する。

## 方針
全ての面と最初の prefix に有限和を分け、同じ境界和へ戻す。

## 規約
theta、比較の元、各列、整数符号を保つ。

## 使われ方
HA 1.2.4。比較射全体の閉性を得るための成分等式。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicTopology
open HomologicalComplex CochainComplex HomComplex SerrePositivity.DifferentialGraded
open scoped _root_.Simplicial
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization
open SerrePositivity.HomologicalAlgebra
open SerrePositivity.InfinityCategories.Project.DerivedCategories
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
variable (A : Type u) [CommRing A] {J : Type} [SmallCategory J]

/-- 比較による後合成は、同じ theta の面の和の符号を保持する。 -/
theorem smallStrictBarColumn_post_signed (F : J ⥤ ModuleCategory A PUnit.{1}) (n : ℕ)
    (s : ((SSet.uliftFunctor.{u, 0}).obj (nerve J)) _⦋n + 1⦌) :
    let L : (moduleHom A PUnit.{1}
        (ForgetEnrichment.to (Complex A)
          (dgCoherentBarFamily A PUnit.{1} (smallStrictBarDiagram A F) ⟨n + 1, s⟩))
        (ForgetEnrichment.to (Complex A)
          (dgCoherentBarGraded A PUnit.{1} (smallStrictBarDiagram A F)))).X 1 →
        Cochain
          ((ForgetEnrichment.to (Complex A)
            (dgCoherentBarFamily A PUnit.{1} (smallStrictBarDiagram A F) ⟨n + 1, s⟩)).obj
            (op PUnit.unit)) ((smallStrictBarTotalTarget A F).obj (op PUnit.unit)) 1 :=
      fun b => (moduleHomπ A PUnit.{1} _ (smallStrictBarTotalTarget A F) PUnit.unit).f 1
        (compose A (D := RightModule A PUnit.{1})
          (smallStrictBarTotalGradedElement A F) b (add_zero 1))
    L (dgCoherentBarColumn A PUnit.{1} (smallStrictBarDiagram A F) ⟨n + 1, s⟩) =
      (∑ i : Fin (n + 1), ((i.val : ℤ) + 1).negOnePow •
        (((n + 1 : ℕ) : ℤ).negOnePow •
          L (dgCoherentBarFaceColumn A PUnit.{1} (smallStrictBarDiagram A F) s i))) +
      ((n + 1 : ℕ) : ℤ).negOnePow •
        L (dgCoherentBarPrefixColumn A PUnit.{1} (smallStrictBarDiagram A F) s 0 (by omega)) := by
  let L : (moduleHom A PUnit.{1}
      (ForgetEnrichment.to (Complex A)
        (dgCoherentBarFamily A PUnit.{1} (smallStrictBarDiagram A F) ⟨n + 1, s⟩))
      (ForgetEnrichment.to (Complex A)
        (dgCoherentBarGraded A PUnit.{1} (smallStrictBarDiagram A F)))).X 1 →+
      Cochain
        ((ForgetEnrichment.to (Complex A)
          (dgCoherentBarFamily A PUnit.{1} (smallStrictBarDiagram A F) ⟨n + 1, s⟩)).obj
          (op PUnit.unit)) ((smallStrictBarTotalTarget A F).obj (op PUnit.unit)) 1 :=
    { toFun b := (moduleHomπ A PUnit.{1} _ (smallStrictBarTotalTarget A F) PUnit.unit).f 1
        (compose A (D := RightModule A PUnit.{1}) (smallStrictBarTotalGradedElement A F) b (add_zero 1))
      map_zero' := by rw [compose_zero, map_zero]
      map_add' b c := by rw [compose_add_right, map_add] }
  change L _ = (∑ i : Fin (n + 1), ((i.val : ℤ) + 1).negOnePow •
    (((n + 1 : ℕ) : ℤ).negOnePow • L _)) + ((n + 1 : ℕ) : ℤ).negOnePow • L _
  have hu (ε : ℤˣ) (b) : L (ε • b) = ε • L b := map_zsmul L (ε : ℤ) b
  rw [smallStrictBarColumn, map_add, map_sum, hu]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [hu, smul_smul, ← Int.negOnePow_add]
  congr 1
  congr 1
  omega

private def unsignedShiftAddHom {K L : Complex A} {a : ℤ} (m r : ℤ) (h : a + m = r) :
    Cochain K L a →+ Cochain (K⟦m⟧) L r where
  toFun z := unsignedLeftShift z m r h
  map_zero' := by simp [unsignedLeftShift]
  map_add' z w := by simp [unsignedLeftShift, Cochain.leftShift_add, smul_add]

/-- 正次数の theta の同じ列を比較した値は、元の列の微分のシフト。 -/
theorem smallStrictBarColumn_post_positive (F : J ⥤ ModuleCategory A PUnit.{1}) (n : ℕ)
    (s : ((SSet.uliftFunctor.{u, 0}).obj (nerve J)) _⦋n + 1⦌) :
    (moduleHomπ A PUnit.{1}
      (ForgetEnrichment.to (Complex A)
        (dgCoherentBarFamily A PUnit.{1} (smallStrictBarDiagram A F) ⟨n + 1, s⟩))
      (smallStrictBarTotalTarget A F) PUnit.unit).f 1
      (compose A (D := RightModule A PUnit.{1})
        (x := ForgetEnrichment.to (Complex A)
          (dgCoherentBarFamily A PUnit.{1} (smallStrictBarDiagram A F) ⟨n + 1, s⟩))
        (y := ForgetEnrichment.to (Complex A)
          (dgCoherentBarGraded A PUnit.{1} (smallStrictBarDiagram A F)))
        (z := smallStrictBarTotalTarget A F) (smallStrictBarTotalGradedElement A F)
        (dgCoherentBarColumn A PUnit.{1} (smallStrictBarDiagram A F) ⟨n + 1, s⟩) (add_zero 1)) =
      unsignedLeftShift
        (δ (-((n + 1 : ℕ) : ℤ)) (-((n + 1 : ℕ) : ℤ) + 1)
          (smallStrictBarUnshiftedColumn A F ⟨n + 1, s⟩))
        ((n + 1 : ℕ) : ℤ) 1 (by omega) := by
  have h := smallStrictBarColumn_post_signed A F n s
  dsimp only at h
  apply h.trans
  let U := unsignedShiftAddHom A
    (K := (smallStrictBarCoefficientDiagram A F).obj (s.down.obj 0))
    (L := (smallStrictBarTotalTarget A F).obj (op PUnit.unit))
    (a := -((n + 1 : ℕ) : ℤ) + 1) ((n + 1 : ℕ) : ℤ) 1 (by omega)
  have hd := congrArg U (smallStrictBarUnshiftedColumn_boundary_sum A F n s)
  rw [map_sum, Fin.sum_univ_succ] at hd
  simp only [map_zsmul, Fin.val_zero, pow_zero, one_smul] at hd
  have h₀ : U (smallStrictBarBoundaryTerm A F n s 0) = _ :=
    smallStrictBarBoundaryTerm_zero_shift A F n s
  have hi (i : Fin (n + 1)) : U (smallStrictBarBoundaryTerm A F n s i.succ) =
      unsignedLeftShift (smallStrictBarUnshiftedColumn A F (dgCoherentBarFace s i.succ))
        ((n + 1 : ℕ) : ℤ) 1 (by
          change -(n : ℤ) + ((n + 1 : ℕ) : ℤ) = 1
          omega) :=
    unsignedLeftShift_of_heq A _ _ (smallStrictBarBoundaryTerm_succ A F n s i) _ _ _ _
  rw [h₀] at hd
  simp only [hi] at hd
  apply Eq.trans _ hd.symm
  apply Eq.trans _ (add_comm _ _)
  apply congrArg₂ (fun a b => a + b)
  · apply Finset.sum_congr rfl
    intro i _
    apply (congrArg (fun z => ((i.val : ℤ) + 1).negOnePow • z)
      (smallStrictBarSignedFaceColumn A F n s i)).trans
    change ((i.val : ℤ) + 1).negOnePow • _ = (-1 : ℤ) ^ i.succ.val • _
    rw [show (i.val : ℤ) + 1 = (i.succ.val : ℤ) by simp]
    simp only [Units.smul_def, Int.coe_negOnePow_natCast]
  · exact smallStrictBarSignedPrefixColumn A F n s

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization
