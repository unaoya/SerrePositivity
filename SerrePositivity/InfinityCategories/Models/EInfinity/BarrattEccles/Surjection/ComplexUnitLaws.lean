module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.ComplexUnit
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ComplexComposition
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.TensorEpimorphism
public import SerrePositivity.EInfinity.BarrattEccles.PartialCompositionLeftUnit
public import SerrePositivity.EInfinity.BarrattEccles.PartialCompositionRightUnit

/-!
模型。文献の定義との比較は後で
# 全射語の複体射の左右単位則

概要：Berger–Fresse §1.2.4 の単位則を非有界整数複体の射として証明する。
方針：TR とテンソル単位の全射を前合成し、合成保存と BE の単位則で比較する。
規約：各全射性は構成済みのものを局所的に使い、cofibrancy は要求しない。
使われ方：χ の Operad の unit_comp と comp_unit。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open _root_.SerrePositivity.DifferentialGraded

variable (A : Type u) [CommRing A]

/-- 概要：整数 TR は arity の等式の射と可換（BF §1.3）。
方針：等式を消去して恒等射の合成を簡約する。
規約：全整数次数の複体射の等式。
使われ方：χ の単位・結合則の arity 移送を BE と比較する。 -/
lemma _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.cochainMap_arity {m n : ℕ} (h : m = n) :
    eqToHom (congrArg (_root_.SerrePositivity.EInfinity.BarrattEccles.complex A) h) ≫ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.cochainMap A n =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.cochainMap A m ≫ eqToHom (congrArg (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complex A) h) := by
  cases h
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

namespace Surjection

open _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction

/-- 概要：χ の整数部分合成は複体射の右単位則を満たす（BF §1.2.4）。
方針：TR とテンソル単位の全射で消去し、BE の合成保存と右単位則を使う。
規約：全 arity・全入力位置。
使われ方：χ の Operad の comp_unit。 -/
lemma _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complexPartialComposition_right_unit (m : ℕ) (i : Fin (m + 1)) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complex A (m + 1) ◁ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complexUnit A) ≫ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complexPartialComposition A m 1 i =
      (ρ_ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complex A (m + 1))).hom := by
  let _ : Epi (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.cochainMap A (m + 1)) := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.cochainMap_epi A (m + 1)
  let _ : Epi (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.cochainMap A (m + 1) ▷ (𝟙_ (Complex A))) :=
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.tensor_epi_of_epi A (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.cochainMap A (m + 1)) (𝟙 (𝟙_ (Complex A)))
  apply (cancel_epi (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.cochainMap A (m + 1) ▷ (𝟙_ (Complex A)))).1
  calc
    _ = (_root_.SerrePositivity.EInfinity.BarrattEccles.complex A (m + 1) ◁ _root_.SerrePositivity.EInfinity.BarrattEccles.unit A) ≫
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.cochainMap A (m + 1) ⊗ₘ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.cochainMap A 1) ≫ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complexPartialComposition A m 1 i := by
      change (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.cochainMap A (m + 1) ⊗ₘ 𝟙 _) ≫
        ((𝟙 _ ⊗ₘ (_root_.SerrePositivity.EInfinity.BarrattEccles.unit A ≫ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.cochainMap A 1)) ≫ _) =
          (𝟙 _ ⊗ₘ _root_.SerrePositivity.EInfinity.BarrattEccles.unit A) ≫ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.cochainMap A (m + 1) ⊗ₘ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.cochainMap A 1) ≫ _
      simp only [← Category.assoc, tensorHom_comp_tensorHom, Category.id_comp, Category.comp_id]
    _ = (_root_.SerrePositivity.EInfinity.BarrattEccles.complex A (m + 1) ◁ _root_.SerrePositivity.EInfinity.BarrattEccles.unit A) ≫
        _root_.SerrePositivity.EInfinity.BarrattEccles.partialComposition A m 1 i ≫ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.cochainMap A (m + 1) := by
      rw [← _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.complexPartialComposition_comm]
    _ = (ρ_ (_root_.SerrePositivity.EInfinity.BarrattEccles.complex A (m + 1))).hom ≫ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.cochainMap A (m + 1) := by
      rw [← Category.assoc, _root_.SerrePositivity.EInfinity.BarrattEccles.partialComposition_right_unit]
    _ = _ := (rightUnitor_naturality (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.cochainMap A (m + 1))).symm

/-- 概要：χ の整数部分合成は複体射の左単位則を満たす（BF §1.2.4）。
方針：単位と TR の全射で消去し、arity 移送と BE の左単位則を使う。
規約：arity 零の演算も含む。
使われ方：χ の Operad の unit_comp。 -/
lemma _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complexPartialComposition_left_unit (n : ℕ) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complexUnit A ▷ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complex A n) ≫ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complexPartialComposition A 0 n 0 ≫
        eqToHom (congrArg (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complex A) (Nat.zero_add n)) = (λ_ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complex A n)).hom := by
  let _ : Epi (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.cochainMap A n) := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.cochainMap_epi A n
  let _ : Epi ((𝟙_ (Complex A)) ◁ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.cochainMap A n) :=
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.tensor_epi_of_epi A (𝟙 (𝟙_ (Complex A))) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.cochainMap A n)
  apply (cancel_epi ((𝟙_ (Complex A)) ◁ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.cochainMap A n)).1
  calc
    _ = (_root_.SerrePositivity.EInfinity.BarrattEccles.unit A ▷ _root_.SerrePositivity.EInfinity.BarrattEccles.complex A n) ≫
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.cochainMap A 1 ⊗ₘ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.cochainMap A n) ≫ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complexPartialComposition A 0 n 0 ≫
          eqToHom (congrArg (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complex A) (Nat.zero_add n)) := by
      change (𝟙 _ ⊗ₘ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.cochainMap A n) ≫
        (((_root_.SerrePositivity.EInfinity.BarrattEccles.unit A ≫ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.cochainMap A 1) ⊗ₘ 𝟙 _) ≫ _ ≫ _) =
          (_root_.SerrePositivity.EInfinity.BarrattEccles.unit A ⊗ₘ 𝟙 _) ≫ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.cochainMap A 1 ⊗ₘ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.cochainMap A n) ≫ _ ≫ _
      simp only [← Category.assoc, tensorHom_comp_tensorHom, Category.id_comp, Category.comp_id]
    _ = (_root_.SerrePositivity.EInfinity.BarrattEccles.unit A ▷ _root_.SerrePositivity.EInfinity.BarrattEccles.complex A n) ≫
        _root_.SerrePositivity.EInfinity.BarrattEccles.partialComposition A 0 n 0 ≫ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.cochainMap A (0 + n) ≫
          eqToHom (congrArg (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complex A) (Nat.zero_add n)) := by
      simpa only [Category.assoc] using congrArg
        (fun f => (_root_.SerrePositivity.EInfinity.BarrattEccles.unit A ▷ _root_.SerrePositivity.EInfinity.BarrattEccles.complex A n) ≫ f ≫
          eqToHom (congrArg (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complex A) (Nat.zero_add n)))
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.complexPartialComposition_comm A 0 n 0).symm
    _ = (_root_.SerrePositivity.EInfinity.BarrattEccles.unit A ▷ _root_.SerrePositivity.EInfinity.BarrattEccles.complex A n) ≫
        _root_.SerrePositivity.EInfinity.BarrattEccles.partialComposition A 0 n 0 ≫
          eqToHom (congrArg (_root_.SerrePositivity.EInfinity.BarrattEccles.complex A) (Nat.zero_add n)) ≫ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.cochainMap A n := by
      rw [← _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.cochainMap_arity A (Nat.zero_add n)]
    _ = (λ_ (_root_.SerrePositivity.EInfinity.BarrattEccles.complex A n)).hom ≫ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.cochainMap A n := by
      simpa only [Category.assoc] using congrArg (fun f => f ≫ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.cochainMap A n)
        (_root_.SerrePositivity.EInfinity.BarrattEccles.partialComposition_left_unit A n)
    _ = _ := (leftUnitor_naturality (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.cochainMap A n)).symm

end Surjection
end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles
