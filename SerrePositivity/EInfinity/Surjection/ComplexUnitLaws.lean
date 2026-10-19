module

public import SerrePositivity.EInfinity.Surjection.ComplexUnit
public import SerrePositivity.EInfinity.TableReduction.ComplexComposition
public import SerrePositivity.EInfinity.TableReduction.TensorEpimorphism
public import SerrePositivity.EInfinity.BarrattEccles.PartialCompositionLeftUnit
public import SerrePositivity.EInfinity.BarrattEccles.PartialCompositionRightUnit

/-!
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

namespace SerrePositivity.EInfinity

open CategoryTheory MonoidalCategory
open SerrePositivity.DifferentialGraded

variable (A : Type u) [CommRing A]

/-- 概要：整数 TR は arity の等式の射と可換（BF §1.3）。
方針：等式を消去して恒等射の合成を簡約する。
規約：全整数次数の複体射の等式。
使われ方：χ の単位・結合則の arity 移送を BE と比較する。 -/
lemma TableReduction.cochainMap_arity {m n : ℕ} (h : m = n) :
    eqToHom (congrArg (BarrattEccles.complex A) h) ≫ TableReduction.cochainMap A n =
      TableReduction.cochainMap A m ≫ eqToHom (congrArg (Surjection.complex A) h) := by
  cases h
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

namespace Surjection

open TableReduction

/-- 概要：χ の整数部分合成は複体射の右単位則を満たす（BF §1.2.4）。
方針：TR とテンソル単位の全射で消去し、BE の合成保存と右単位則を使う。
規約：全 arity・全入力位置。
使われ方：χ の Operad の comp_unit。 -/
lemma complexPartialComposition_right_unit (m : ℕ) (i : Fin (m + 1)) :
    (complex A (m + 1) ◁ complexUnit A) ≫ complexPartialComposition A m 1 i =
      (ρ_ (complex A (m + 1))).hom := by
  let _ : Epi (cochainMap A (m + 1)) := cochainMap_epi A (m + 1)
  let _ : Epi (cochainMap A (m + 1) ▷ (𝟙_ (Complex A))) :=
    tensor_epi_of_epi A (cochainMap A (m + 1)) (𝟙 (𝟙_ (Complex A)))
  apply (cancel_epi (cochainMap A (m + 1) ▷ (𝟙_ (Complex A)))).1
  calc
    _ = (BarrattEccles.complex A (m + 1) ◁ BarrattEccles.unit A) ≫
        (cochainMap A (m + 1) ⊗ₘ cochainMap A 1) ≫ complexPartialComposition A m 1 i := by
      change (cochainMap A (m + 1) ⊗ₘ 𝟙 _) ≫
        ((𝟙 _ ⊗ₘ (BarrattEccles.unit A ≫ cochainMap A 1)) ≫ _) =
          (𝟙 _ ⊗ₘ BarrattEccles.unit A) ≫ (cochainMap A (m + 1) ⊗ₘ cochainMap A 1) ≫ _
      simp only [← Category.assoc, tensorHom_comp_tensorHom, Category.id_comp, Category.comp_id]
    _ = (BarrattEccles.complex A (m + 1) ◁ BarrattEccles.unit A) ≫
        BarrattEccles.partialComposition A m 1 i ≫ cochainMap A (m + 1) := by
      rw [← complexPartialComposition_comm]
    _ = (ρ_ (BarrattEccles.complex A (m + 1))).hom ≫ cochainMap A (m + 1) := by
      rw [← Category.assoc, BarrattEccles.partialComposition_right_unit]
    _ = _ := (rightUnitor_naturality (cochainMap A (m + 1))).symm

/-- 概要：χ の整数部分合成は複体射の左単位則を満たす（BF §1.2.4）。
方針：単位と TR の全射で消去し、arity 移送と BE の左単位則を使う。
規約：arity 零の演算も含む。
使われ方：χ の Operad の unit_comp。 -/
lemma complexPartialComposition_left_unit (n : ℕ) :
    (complexUnit A ▷ complex A n) ≫ complexPartialComposition A 0 n 0 ≫
        eqToHom (congrArg (complex A) (Nat.zero_add n)) = (λ_ (complex A n)).hom := by
  let _ : Epi (cochainMap A n) := cochainMap_epi A n
  let _ : Epi ((𝟙_ (Complex A)) ◁ cochainMap A n) :=
    tensor_epi_of_epi A (𝟙 (𝟙_ (Complex A))) (cochainMap A n)
  apply (cancel_epi ((𝟙_ (Complex A)) ◁ cochainMap A n)).1
  calc
    _ = (BarrattEccles.unit A ▷ BarrattEccles.complex A n) ≫
        (cochainMap A 1 ⊗ₘ cochainMap A n) ≫ complexPartialComposition A 0 n 0 ≫
          eqToHom (congrArg (complex A) (Nat.zero_add n)) := by
      change (𝟙 _ ⊗ₘ cochainMap A n) ≫
        (((BarrattEccles.unit A ≫ cochainMap A 1) ⊗ₘ 𝟙 _) ≫ _ ≫ _) =
          (BarrattEccles.unit A ⊗ₘ 𝟙 _) ≫ (cochainMap A 1 ⊗ₘ cochainMap A n) ≫ _ ≫ _
      simp only [← Category.assoc, tensorHom_comp_tensorHom, Category.id_comp, Category.comp_id]
    _ = (BarrattEccles.unit A ▷ BarrattEccles.complex A n) ≫
        BarrattEccles.partialComposition A 0 n 0 ≫ cochainMap A (0 + n) ≫
          eqToHom (congrArg (complex A) (Nat.zero_add n)) := by
      simpa only [Category.assoc] using congrArg
        (fun f => (BarrattEccles.unit A ▷ BarrattEccles.complex A n) ≫ f ≫
          eqToHom (congrArg (complex A) (Nat.zero_add n)))
        (complexPartialComposition_comm A 0 n 0).symm
    _ = (BarrattEccles.unit A ▷ BarrattEccles.complex A n) ≫
        BarrattEccles.partialComposition A 0 n 0 ≫
          eqToHom (congrArg (BarrattEccles.complex A) (Nat.zero_add n)) ≫ cochainMap A n := by
      rw [← cochainMap_arity A (Nat.zero_add n)]
    _ = (λ_ (BarrattEccles.complex A n)).hom ≫ cochainMap A n := by
      simpa only [Category.assoc] using congrArg (fun f => f ≫ cochainMap A n)
        (BarrattEccles.partialComposition_left_unit A n)
    _ = _ := (leftUnitor_naturality (cochainMap A n)).symm

end Surjection
end SerrePositivity.EInfinity
