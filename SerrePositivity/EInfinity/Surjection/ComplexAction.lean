module

public import SerrePositivity.EInfinity.Surjection.Complex
public import SerrePositivity.EInfinity.Surjection.DeletionDifferential

/-!
# 全射語複体上の対称群作用

概要：Berger–Fresse §1.2.1–3 の値の置換作用を実際の複体の射へまとめる。
方針：削除微分の同変性で非負鎖作用を作り、整数コチェインへ零延長する。
規約：値の左作用であり、σ*τ は先に τ、次に σ を作用させる。
使われ方：χ の複体の対称列と TR の自然性。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity.Surjection

open CategoryTheory

variable (A : Type u) [CommRing A]

/-- 概要：値の置換による χ の非負鎖複体の自己射（BF §1.2.1–3）。
方針：全次数の renameLinear を削除微分との可換性で束ねる。
規約：全 arity を含む左作用。
使われ方：整数コチェイン作用の延長前の射。 -/
def normalizedRename (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    normalizedChains A n ⟶ normalizedChains A n :=
  ChainComplex.ofHom (fun _ => ModuleCat.ofHom (renameLinear A σ)) (fun d => by
    rw [normalizedChains_d]
    apply ModuleCat.hom_ext
    exact differential_renameLinear A n d σ)

/-- 概要：非負鎖置換の成分は既存の renameLinear（BF §1.2.1）。
方針：構成した鎖射の成分を評価する。
規約：次数は任意。
使われ方：作用と TR の成分比較。 -/
@[simp] lemma normalizedRename_f (n d : ℕ) (σ : Equiv.Perm (Fin n)) :
    (normalizedRename A n σ).f d = ModuleCat.ofHom (renameLinear A σ) := rfl

/-- 概要：単位置換の非負鎖作用は恒等射（BF §1.2.1）。
方針：各次数で線形作用の単位則を使う。
規約：arity 零も含む。
使われ方：対称列の恒等射保存。 -/
@[simp] lemma normalizedRename_one (n : ℕ) : normalizedRename A n 1 = 𝟙 _ := by
  ext d : 1
  apply ModuleCat.hom_ext
  exact renameLinear_one A n d

/-- 概要：非負鎖の値の置換は積を保存（BF §1.2.1）。
方針：各次数の線形作用の積を比較する。
規約：カテゴリーの合成では τ の後に σ と書く。
使われ方：対称列の合成保存。 -/
lemma normalizedRename_mul (n : ℕ) (σ τ : Equiv.Perm (Fin n)) :
    normalizedRename A n (σ * τ) = normalizedRename A n τ ≫ normalizedRename A n σ := by
  ext d : 1
  apply ModuleCat.hom_ext
  exact renameLinear_mul A σ τ

/-- 概要：χ(n) の整数コチェイン上の値の置換（BF §1.2.1–3）。
方針：非負鎖作用を次数 q ↦ −q の延長関手で送る。
規約：値の共変な左作用。
使われ方：χ の対称列の構造射。 -/
def complexRename (n : ℕ) (σ : Equiv.Perm (Fin n)) : complex A n ⟶ complex A n :=
  (ComplexShape.embeddingDownNat.extendFunctor (ModuleCat A)).map (normalizedRename A n σ)

/-- 概要：整数複体の単位置換作用は恒等射（BF §1.2.1）。
方針：鎖作用の単位則を延長関手で送る。
規約：全整数次数。
使われ方：χ の対称列の恒等射保存。 -/
@[simp] lemma complexRename_one (n : ℕ) : complexRename A n 1 = 𝟙 _ := by
  simp only [complexRename, normalizedRename_one, CategoryTheory.Functor.map_id]
  rfl

/-- 概要：整数複体の値の置換も積を保存（BF §1.2.1）。
方針：鎖作用の積の法則を延長関手で送る。
規約：先に τ、次に σ を作用させる。
使われ方：χ の対称列の合成保存。 -/
lemma complexRename_mul (n : ℕ) (σ τ : Equiv.Perm (Fin n)) :
    complexRename A n (σ * τ) = complexRename A n τ ≫ complexRename A n σ := by
  simp only [complexRename, normalizedRename_mul, CategoryTheory.Functor.map_comp]

end SerrePositivity.EInfinity.Surjection
