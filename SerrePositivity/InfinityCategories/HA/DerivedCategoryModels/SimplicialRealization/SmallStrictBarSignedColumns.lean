module

public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization.SmallStrictBarBlockCoefficients
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization.SmallStrictBarTotalComposition
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization.SignedShiftBlockComposition
import all SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization.SmallStrictBarTotalColumns
import all SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization.SmallStrictBarBlockCoefficients
import all SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.CoherentBar.Structure.DGCoherentBarDifferential

/-!
# 同じ theta の符号つき面の列の後合成

## 概要
比較を元の面の列へ後合成した値を、一つ下の同じ列のシフトへ戻す。

## 方針
同じ余積因子への制限、shift ブロックの評価と単位係数の公式を合成する。

## 規約
bar の外側の符号を含め、同じ元の列とすべての面を保持する。

## 使われ方
HA 1.2.4。比較射の閉性の theta 側の成分計算。
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
variable (A : Type u) [CommRing A] {J : Type} [SmallCategory J]
variable (F : J ⥤ ModuleCategory A PUnit.{1})

private theorem postSignedBlock
    (s : dgCoherentBarIndex ((SSet.uliftFunctor.{u, 0}).obj (nerve J)))
    (M : ModuleCategory A PUnit.{1}) (ε : ℤˣ)
    (b : (moduleHom A PUnit.{1} (ForgetEnrichment.to (Complex A) M)
      (ForgetEnrichment.to (Complex A) (dgCoherentBarFamily A PUnit.{1} (smallStrictBarDiagram A F) s))).X 1) :
    ε • (moduleHomπ A PUnit.{1} (ForgetEnrichment.to (Complex A) M)
      (smallStrictBarTotalTarget A F) PUnit.unit).f 1
      (compose A (smallStrictBarTotalGradedElement A F)
        ((eHomWhiskerLeft (Complex A) M
          (Sigma.ι (dgCoherentBarFamily A PUnit.{1} (smallStrictBarDiagram A F)) s)).f 1 b)
        (add_zero 1)) =
    ((moduleHomπ A PUnit.{1} (ForgetEnrichment.to (Complex A) M)
      (ForgetEnrichment.to (Complex A) (dgCoherentBarFamily A PUnit.{1} (smallStrictBarDiagram A F) s))
      PUnit.unit).f 1 (ε • b)).comp
      ((moduleHomπ A PUnit.{1}
        (ForgetEnrichment.to (Complex A) (dgCoherentBarFamily A PUnit.{1} (smallStrictBarDiagram A F) s))
        (smallStrictBarTotalTarget A F) PUnit.unit).f 0 (smallStrictBarTotalColumn A F s)) (add_zero 1) := by
  let π := (moduleHomπ A PUnit.{1} (ForgetEnrichment.to (Complex A) M)
    (ForgetEnrichment.to (Complex A) (dgCoherentBarFamily A PUnit.{1} (smallStrictBarDiagram A F) s))
    PUnit.unit).f 1
  let c := (moduleHomπ A PUnit.{1}
    (ForgetEnrichment.to (Complex A) (dgCoherentBarFamily A PUnit.{1} (smallStrictBarDiagram A F) s))
    (smallStrictBarTotalTarget A F) PUnit.unit).f 0 (smallStrictBarTotalColumn A F s)
  have hπ : π (ε • b) = ε • π b := map_zsmul π.hom (ε : ℤ) b
  exact (congrArg (fun z => ε • z)
    (smallStrictBarTotalGradedElement_postBlock A F s M 1 b)).trans
      ((Cochain.units_smul_comp ε (π b) c (add_zero 1)).symm.trans
        (congrArg (fun z => z.comp c (add_zero 1)) hπ.symm))

/-- 元の先頭を保つ面の列の後合成は、同じ面の列のシフトへ戻る。 -/
theorem smallStrictBarSignedFaceColumn (n : ℕ)
    (s : ((SSet.uliftFunctor.{u, 0}).obj (nerve J)) _⦋n + 1⦌) (i : Fin (n + 1)) :
    ((n + 1 : ℕ) : ℤ).negOnePow •
      (moduleHomπ A PUnit.{1}
        (ForgetEnrichment.to (Complex A)
          (dgCoherentBarFamily A PUnit.{1} (smallStrictBarDiagram A F) ⟨n + 1, s⟩))
        (smallStrictBarTotalTarget A F) PUnit.unit).f 1
        (compose A (D := RightModule A PUnit.{1})
          (x := ForgetEnrichment.to (Complex A)
            (dgCoherentBarFamily A PUnit.{1} (smallStrictBarDiagram A F) ⟨n + 1, s⟩))
          (y := ForgetEnrichment.to (Complex A)
            (dgCoherentBarGraded A PUnit.{1} (smallStrictBarDiagram A F)))
          (z := smallStrictBarTotalTarget A F)
          (smallStrictBarTotalGradedElement A F)
          (dgCoherentBarFaceColumn A PUnit.{1} (smallStrictBarDiagram A F) s i) (add_zero 1)) =
      unsignedLeftShift (smallStrictBarUnshiftedColumn A F (dgCoherentBarFace s i.succ))
        ((n + 1 : ℕ) : ℤ) 1 (by
          change -(n : ℤ) + ((n + 1 : ℕ) : ℤ) = 1
          omega) := by
  have hb := eq_of_heq (smallStrictBarFaceBlock_heq A F s i)
  have h := postSignedBlock A F (dgCoherentBarFace s i.succ)
    (dgCoherentBarFamily A PUnit.{1} (smallStrictBarDiagram A F) ⟨n + 1, s⟩)
    ((n + 1 : ℕ) : ℤ).negOnePow
    (dgCoherentBarFaceBlock A PUnit.{1} (smallStrictBarDiagram A F) s i)
  apply h.trans
  let π := (moduleHomπ A PUnit.{1}
    (ForgetEnrichment.to (Complex A)
      (dgCoherentBarFamily A PUnit.{1} (smallStrictBarDiagram A F) ⟨n + 1, s⟩))
    (ForgetEnrichment.to (Complex A)
      (dgCoherentBarFamily A PUnit.{1} (smallStrictBarDiagram A F) (dgCoherentBarFace s i.succ)))
    PUnit.unit).f 1
  let c := (moduleHomπ A PUnit.{1}
    (ForgetEnrichment.to (Complex A)
      (dgCoherentBarFamily A PUnit.{1} (smallStrictBarDiagram A F) (dgCoherentBarFace s i.succ)))
    (smallStrictBarTotalTarget A F) PUnit.unit).f 0
      (smallStrictBarTotalColumn A F (dgCoherentBarFace s i.succ))
  have h₁ := congrArg (fun b => (π (((n + 1 : ℕ) : ℤ).negOnePow • b)).comp c (add_zero 1)) hb
  apply h₁.trans
  let M₀ := ForgetEnrichment.to (Complex A) (F.obj (s.down.obj 0))
  let ψ := (moduleHomπ A PUnit.{1} (shiftModule ((n + 1 : ℕ) : ℤ) M₀)
    (shiftModule (n : ℤ) M₀) PUnit.unit).f 1
  let b₀ := moduleHomShiftBlock A PUnit.{1} ((n + 1 : ℕ) : ℤ) (n : ℤ)
    (unitElement A M₀).val (k := 1) (by omega)
  have h₂ := congrArg (fun z => (ψ (((n + 1 : ℕ) : ℤ).negOnePow • b₀)).comp z (add_zero 1))
    (smallStrictBarTotalColumn_point A F (dgCoherentBarFace s i.succ))
  apply h₂.trans
  have hc := signedShiftBlock_comp A n
    (ForgetEnrichment.to (Complex A) (F.obj (s.down.obj 0)))
    (ForgetEnrichment.to (Complex A) (F.obj (s.down.obj 0)))
    ((smallStrictBarTotalTarget A F).obj (op PUnit.unit))
    (unitElement A (ForgetEnrichment.to (Complex A) (F.obj (s.down.obj 0)))).val
    (smallStrictBarUnshiftedColumn A F (dgCoherentBarFace s i.succ))
  have hi := congrArg (fun g => g.comp
    (smallStrictBarUnshiftedColumn A F (dgCoherentBarFace s i.succ)) (zero_add (-(n : ℤ))))
    (yoneda_moduleUnit_π A PUnit.{1} M₀ PUnit.unit)
  have hunit := hi.trans
    (Cochain.id_comp (smallStrictBarUnshiftedColumn A F (dgCoherentBarFace s i.succ)))
  exact hc.trans (congrArg (fun z : Cochain (M₀.obj (op PUnit.unit))
    ((smallStrictBarTotalTarget A F).obj (op PUnit.unit)) (-(n : ℤ)) =>
      unsignedLeftShift z ((n + 1 : ℕ) : ℤ) 1 (by omega)) hunit)

/-- 最初の prefix の係数の一点評価は、元の strict 図式の同じ射の cochain。 -/
theorem smallStrictBarPrefixHom_point (n : ℕ)
    (s : ((SSet.uliftFunctor.{u, 0}).obj (nerve J)) _⦋n + 1⦌) :
    (moduleHomπ A PUnit.{1}
      (dgCoherentBarSource A PUnit.{1} (smallStrictBarDiagram A F) ⟨n + 1, s⟩)
      (dgCoherentBarSource A PUnit.{1} (smallStrictBarDiagram A F) (dgCoherentBarTail s 1 (by omega)))
      PUnit.unit).f 0
      (dgCoherentBarPrefixHom A PUnit.{1} (smallStrictBarDiagram A F) s 0 (by omega)) =
    Cochain.ofHom ((smallStrictBarCoefficientDiagram A F).map
      (s.down.map (homOfLE (Fin.zero_le (Fin.succ (0 : Fin (n + 1))))))) := by
  have hb := eq_of_heq (smallStrictBarPrefixHom_zero A F s)
  let π := (moduleHomπ A PUnit.{1}
    (dgCoherentBarSource A PUnit.{1} (smallStrictBarDiagram A F) ⟨n + 1, s⟩)
    (dgCoherentBarSource A PUnit.{1} (smallStrictBarDiagram A F) (dgCoherentBarTail s 1 (by omega)))
    PUnit.unit).f 0
  apply (congrArg (fun z => π z) hb).trans
  apply Cochain.ext
  intro p q hpq
  have hq : q = p := by omega
  cases hq
  rfl

set_option maxHeartbeats 800000 in
-- tail の端点と shift の複数の次数同型の照合に必要。
/-- 元の最初の prefix の列の後合成は、同じ先頭の射の後の列のシフト。 -/
theorem smallStrictBarSignedPrefixColumn (n : ℕ)
    (s : ((SSet.uliftFunctor.{u, 0}).obj (nerve J)) _⦋n + 1⦌) :
    ((n + 1 : ℕ) : ℤ).negOnePow •
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
          (dgCoherentBarPrefixColumn A PUnit.{1} (smallStrictBarDiagram A F) s 0 (by omega))
          (add_zero 1)) =
    unsignedLeftShift
      ((Cochain.ofHom ((smallStrictBarCoefficientDiagram A F).map
        (s.down.map (homOfLE (Fin.zero_le (Fin.succ (0 : Fin (n + 1)))))))).comp
        (smallStrictBarUnshiftedColumn A F (dgCoherentBarTail s 1 (by omega))) (zero_add _))
      ((n + 1 : ℕ) : ℤ) 1 (by
        change -(n : ℤ) + ((n + 1 : ℕ) : ℤ) = 1
        omega) := by
  let t := dgCoherentBarTail s 1 (by omega)
  let M₀ := dgCoherentBarSource A PUnit.{1} (smallStrictBarDiagram A F) ⟨n + 1, s⟩
  let N₀ := dgCoherentBarSource A PUnit.{1} (smallStrictBarDiagram A F) t
  let f := dgCoherentBarPrefixHom A PUnit.{1} (smallStrictBarDiagram A F) s 0 (by omega)
  let ψ := (moduleHomπ A PUnit.{1} (shiftModule ((n + 1 : ℕ) : ℤ) M₀)
    (shiftModule (n : ℤ) N₀) PUnit.unit).f 1
  let b := moduleHomShiftBlock A PUnit.{1} ((n + 1 : ℕ) : ℤ) (n : ℤ) f (k := 1) (by omega)
  have h := postSignedBlock A F t
    (dgCoherentBarFamily A PUnit.{1} (smallStrictBarDiagram A F) ⟨n + 1, s⟩)
    ((n + 1 : ℕ) : ℤ).negOnePow
    (dgCoherentBarPrefixBlock A PUnit.{1} (smallStrictBarDiagram A F) s 0 (by omega))
  apply h.trans
  have h₂ := congrArg (fun z => (ψ (((n + 1 : ℕ) : ℤ).negOnePow • b)).comp z (add_zero 1))
    (smallStrictBarTotalColumn_point A F t)
  apply h₂.trans
  have hc := signedShiftBlock_comp A n M₀ N₀
    ((smallStrictBarTotalTarget A F).obj (op PUnit.unit)) f (smallStrictBarUnshiftedColumn A F t)
  apply hc.trans
  have hf := congrArg (fun z => z.comp (smallStrictBarUnshiftedColumn A F t) (zero_add (-(n : ℤ))))
    (smallStrictBarPrefixHom_point A F n s)
  exact congrArg (fun z : Cochain (M₀.obj (op PUnit.unit))
    ((smallStrictBarTotalTarget A F).obj (op PUnit.unit)) (-(n : ℤ)) =>
      unsignedLeftShift z ((n + 1 : ℕ) : ℤ) 1 (by omega)) hf

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization
