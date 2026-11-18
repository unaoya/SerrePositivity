module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ComplexComposition
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.TensorEpimorphism
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.SequenceMap
public import SerrePositivity.EInfinity.BarrattEccles.PartialCompositionEquivariance

/-!
模型。文献の定義との比較は後で
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

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction
open _root_.SerrePositivity.DifferentialGraded

variable (A : Type u) [CommRing A]

/-- 概要：χ の複体射の部分合成は内側の逆左作用について同変（BF §1.2.4・§1.3.6）。
方針：TR のテンソルを前合成し、合成保存と BE の右作用同変性を連結する。
規約：零 arity の挿入区間を含む。
使われ方：χ の inner_equivariance の複体射の法則。 -/
lemma complexPartialComposition_inner_rightAction (m n : ℕ) (i : Fin (m + 1))
    (κ : Equiv.Perm (Fin n)) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complex A (m + 1) ◁ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complexRename A n κ⁻¹) ≫ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complexPartialComposition A m n i =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complexPartialComposition A m n i ≫
        _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complexRename A (m + n) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadInnerPermutation m n i κ)⁻¹ := by
  let _ := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.tensor_cochainMap_epi A (m + 1) n
  apply (cancel_epi (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.cochainMap A (m + 1) ⊗ₘ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.cochainMap A n)).1
  calc
    _ = (_root_.SerrePositivity.EInfinity.BarrattEccles.complex A (m + 1) ◁ _root_.SerrePositivity.EInfinity.BarrattEccles.complexRightAction A n κ) ≫
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.cochainMap A (m + 1) ⊗ₘ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.cochainMap A n) ≫ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complexPartialComposition A m n i := by
      change (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.cochainMap A (m + 1) ⊗ₘ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.cochainMap A n) ≫
        ((𝟙 _ ⊗ₘ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complexRename A n κ⁻¹) ≫ _) =
          (𝟙 _ ⊗ₘ _root_.SerrePositivity.EInfinity.BarrattEccles.complexRightAction A n κ) ≫
            (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.cochainMap A (m + 1) ⊗ₘ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.cochainMap A n) ≫ _
      simp only [← Category.assoc, tensorHom_comp_tensorHom, Category.id_comp, Category.comp_id]
      rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.cochainMap_rightAction A n κ]
    _ = (_root_.SerrePositivity.EInfinity.BarrattEccles.complex A (m + 1) ◁ _root_.SerrePositivity.EInfinity.BarrattEccles.complexRightAction A n κ) ≫
        _root_.SerrePositivity.EInfinity.BarrattEccles.partialComposition A m n i ≫ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.cochainMap A (m + n) := by
      rw [← _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.complexPartialComposition_comm]
    _ = _root_.SerrePositivity.EInfinity.BarrattEccles.partialComposition A m n i ≫
        _root_.SerrePositivity.EInfinity.BarrattEccles.complexRightAction A (m + n) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadInnerPermutation m n i κ) ≫
          _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.cochainMap A (m + n) := by
      simpa only [Category.assoc] using congrArg (fun f => f ≫ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.cochainMap A (m + n))
        (_root_.SerrePositivity.EInfinity.BarrattEccles.partialComposition_inner_rightAction A m n i κ)
    _ = _root_.SerrePositivity.EInfinity.BarrattEccles.partialComposition A m n i ≫ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.cochainMap A (m + n) ≫
        _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complexRename A (m + n) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadInnerPermutation m n i κ)⁻¹ := by
      rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.cochainMap_rightAction]
    _ = _ := by
      simpa only [Category.assoc] using congrArg
        (fun f => f ≫ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complexRename A (m + n) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadInnerPermutation m n i κ)⁻¹)
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.complexPartialComposition_comm A m n i)

/-- 概要：χ の複体射の部分合成は外側の逆左作用について同変（BF §1.2.4・§1.3.6）。
方針：TR の二因子の全射で消去し、BE の位置移送を伴う同変性を使う。
規約：外側作用前の挿入位置は ρ(i)。
使われ方：χ の outer_equivariance の複体射の法則。 -/
lemma complexPartialComposition_outer_rightAction (m n : ℕ) (i : Fin (m + 1))
    (ρ : Equiv.Perm (Fin (m + 1))) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complexRename A (m + 1) ρ⁻¹ ▷ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complex A n) ≫ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complexPartialComposition A m n i =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complexPartialComposition A m n (ρ i) ≫
        _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complexRename A (m + n) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadOuterPermutation m n i ρ)⁻¹ := by
  let _ := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.tensor_cochainMap_epi A (m + 1) n
  apply (cancel_epi (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.cochainMap A (m + 1) ⊗ₘ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.cochainMap A n)).1
  calc
    _ = (_root_.SerrePositivity.EInfinity.BarrattEccles.complexRightAction A (m + 1) ρ ▷ _root_.SerrePositivity.EInfinity.BarrattEccles.complex A n) ≫
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.cochainMap A (m + 1) ⊗ₘ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.cochainMap A n) ≫ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complexPartialComposition A m n i := by
      change (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.cochainMap A (m + 1) ⊗ₘ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.cochainMap A n) ≫
        ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complexRename A (m + 1) ρ⁻¹ ⊗ₘ 𝟙 _) ≫ _) =
          (_root_.SerrePositivity.EInfinity.BarrattEccles.complexRightAction A (m + 1) ρ ⊗ₘ 𝟙 _) ≫
            (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.cochainMap A (m + 1) ⊗ₘ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.cochainMap A n) ≫ _
      simp only [← Category.assoc, tensorHom_comp_tensorHom, Category.id_comp, Category.comp_id]
      rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.cochainMap_rightAction A (m + 1) ρ]
    _ = (_root_.SerrePositivity.EInfinity.BarrattEccles.complexRightAction A (m + 1) ρ ▷ _root_.SerrePositivity.EInfinity.BarrattEccles.complex A n) ≫
        _root_.SerrePositivity.EInfinity.BarrattEccles.partialComposition A m n i ≫ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.cochainMap A (m + n) := by
      rw [← _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.complexPartialComposition_comm]
    _ = _root_.SerrePositivity.EInfinity.BarrattEccles.partialComposition A m n (ρ i) ≫
        _root_.SerrePositivity.EInfinity.BarrattEccles.complexRightAction A (m + n) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadOuterPermutation m n i ρ) ≫
          _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.cochainMap A (m + n) := by
      simpa only [Category.assoc] using congrArg (fun f => f ≫ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.cochainMap A (m + n))
        (_root_.SerrePositivity.EInfinity.BarrattEccles.partialComposition_outer_rightAction A m n i ρ)
    _ = _root_.SerrePositivity.EInfinity.BarrattEccles.partialComposition A m n (ρ i) ≫ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.cochainMap A (m + n) ≫
        _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complexRename A (m + n) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadOuterPermutation m n i ρ)⁻¹ := by
      rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.cochainMap_rightAction]
    _ = _ := by
      simpa only [Category.assoc] using congrArg
        (fun f => f ≫ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complexRename A (m + n) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadOuterPermutation m n i ρ)⁻¹)
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.complexPartialComposition_comm A m n (ρ i))

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection
