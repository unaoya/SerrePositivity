module

public import SerrePositivity.EInfinity.TableReduction.ComplexComposition
public import SerrePositivity.EInfinity.TableReduction.TensorEpimorphism
public import SerrePositivity.EInfinity.TableReduction.SequenceMap
public import SerrePositivity.EInfinity.BarrattEccles.PartialCompositionEquivariance

/-!
# 全射語の複体射の内外置換同変性

概要：Berger–Fresse §1.2.4・§1.3.6 の同変性を整数部分合成射について証明する。
方針：TR の二因子テンソルの全射で消去し、BE の同変性と TR の自然性を使う。
規約：右作用の置換 κ は値の左作用 κ⁻¹ として書く。
使われ方：χ の Operad の内外同変性。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity.Surjection

open CategoryTheory MonoidalCategory TableReduction
open SerrePositivity.DifferentialGraded

variable (A : Type u) [CommRing A]

/-- 概要：χ の複体射の部分合成は内側の逆左作用について同変（BF §1.2.4・§1.3.6）。
方針：TR のテンソルを前合成し、合成保存と BE の右作用同変性を連結する。
規約：零 arity の挿入区間を含む。
使われ方：χ の inner_equivariance の複体射の法則。 -/
lemma complexPartialComposition_inner_rightAction (m n : ℕ) (i : Fin (m + 1))
    (κ : Equiv.Perm (Fin n)) :
    (complex A (m + 1) ◁ complexRename A n κ⁻¹) ≫ complexPartialComposition A m n i =
      complexPartialComposition A m n i ≫
        complexRename A (m + n) (operadInnerPermutation m n i κ)⁻¹ := by
  let _ := tensor_cochainMap_epi A (m + 1) n
  apply (cancel_epi (cochainMap A (m + 1) ⊗ₘ cochainMap A n)).1
  calc
    _ = (BarrattEccles.complex A (m + 1) ◁ BarrattEccles.complexRightAction A n κ) ≫
        (cochainMap A (m + 1) ⊗ₘ cochainMap A n) ≫ complexPartialComposition A m n i := by
      change (cochainMap A (m + 1) ⊗ₘ cochainMap A n) ≫
        ((𝟙 _ ⊗ₘ complexRename A n κ⁻¹) ≫ _) =
          (𝟙 _ ⊗ₘ BarrattEccles.complexRightAction A n κ) ≫
            (cochainMap A (m + 1) ⊗ₘ cochainMap A n) ≫ _
      simp only [← Category.assoc, tensorHom_comp_tensorHom, Category.id_comp, Category.comp_id]
      rw [cochainMap_rightAction A n κ]
    _ = (BarrattEccles.complex A (m + 1) ◁ BarrattEccles.complexRightAction A n κ) ≫
        BarrattEccles.partialComposition A m n i ≫ cochainMap A (m + n) := by
      rw [← complexPartialComposition_comm]
    _ = BarrattEccles.partialComposition A m n i ≫
        BarrattEccles.complexRightAction A (m + n) (operadInnerPermutation m n i κ) ≫
          cochainMap A (m + n) := by
      simpa only [Category.assoc] using congrArg (fun f => f ≫ cochainMap A (m + n))
        (BarrattEccles.partialComposition_inner_rightAction A m n i κ)
    _ = BarrattEccles.partialComposition A m n i ≫ cochainMap A (m + n) ≫
        complexRename A (m + n) (operadInnerPermutation m n i κ)⁻¹ := by
      rw [cochainMap_rightAction]
    _ = _ := by
      simpa only [Category.assoc] using congrArg
        (fun f => f ≫ complexRename A (m + n) (operadInnerPermutation m n i κ)⁻¹)
        (complexPartialComposition_comm A m n i)

/-- 概要：χ の複体射の部分合成は外側の逆左作用について同変（BF §1.2.4・§1.3.6）。
方針：TR の二因子の全射で消去し、BE の位置移送を伴う同変性を使う。
規約：外側作用前の挿入位置は ρ(i)。
使われ方：χ の outer_equivariance の複体射の法則。 -/
lemma complexPartialComposition_outer_rightAction (m n : ℕ) (i : Fin (m + 1))
    (ρ : Equiv.Perm (Fin (m + 1))) :
    (complexRename A (m + 1) ρ⁻¹ ▷ complex A n) ≫ complexPartialComposition A m n i =
      complexPartialComposition A m n (ρ i) ≫
        complexRename A (m + n) (operadOuterPermutation m n i ρ)⁻¹ := by
  let _ := tensor_cochainMap_epi A (m + 1) n
  apply (cancel_epi (cochainMap A (m + 1) ⊗ₘ cochainMap A n)).1
  calc
    _ = (BarrattEccles.complexRightAction A (m + 1) ρ ▷ BarrattEccles.complex A n) ≫
        (cochainMap A (m + 1) ⊗ₘ cochainMap A n) ≫ complexPartialComposition A m n i := by
      change (cochainMap A (m + 1) ⊗ₘ cochainMap A n) ≫
        ((complexRename A (m + 1) ρ⁻¹ ⊗ₘ 𝟙 _) ≫ _) =
          (BarrattEccles.complexRightAction A (m + 1) ρ ⊗ₘ 𝟙 _) ≫
            (cochainMap A (m + 1) ⊗ₘ cochainMap A n) ≫ _
      simp only [← Category.assoc, tensorHom_comp_tensorHom, Category.id_comp, Category.comp_id]
      rw [cochainMap_rightAction A (m + 1) ρ]
    _ = (BarrattEccles.complexRightAction A (m + 1) ρ ▷ BarrattEccles.complex A n) ≫
        BarrattEccles.partialComposition A m n i ≫ cochainMap A (m + n) := by
      rw [← complexPartialComposition_comm]
    _ = BarrattEccles.partialComposition A m n (ρ i) ≫
        BarrattEccles.complexRightAction A (m + n) (operadOuterPermutation m n i ρ) ≫
          cochainMap A (m + n) := by
      simpa only [Category.assoc] using congrArg (fun f => f ≫ cochainMap A (m + n))
        (BarrattEccles.partialComposition_outer_rightAction A m n i ρ)
    _ = BarrattEccles.partialComposition A m n (ρ i) ≫ cochainMap A (m + n) ≫
        complexRename A (m + n) (operadOuterPermutation m n i ρ)⁻¹ := by
      rw [cochainMap_rightAction]
    _ = _ := by
      simpa only [Category.assoc] using congrArg
        (fun f => f ≫ complexRename A (m + n) (operadOuterPermutation m n i ρ)⁻¹)
        (complexPartialComposition_comm A m n (ρ i))

end SerrePositivity.EInfinity.Surjection
