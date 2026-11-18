module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.TensorPowerAppendCoherence

/-!
模型。文献の定義との比較は後で
# 二列への分離と二ブロックの連結

概要：Berger–Fresse §3.1 の評価のブロック分解に使う分離同型の連結則を証明する。
方針：前半ブロックの長さで帰納し、単位・結合の図式補題へ帰着する。
規約：両ブロックとも空を許し、arity の移送を明示する。
使われ方：反復評価とテンソル冪の代入の両立を証明する。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.TensorPowers

variable {A : Type u} [CommRing A]

attribute [local irreducible] HomologicalComplex.monoidalCategoryStruct
attribute [local implicit_reducible] _root_.SerrePositivity.TensorPowers.power

/-- 概要：分離同型は arity の等式による移送と可換（BF §3.1）。
方針：等式を帰納して恒等射とテンソルの恒等射則へ帰着する。
規約：両列を同じ arity の等式で移す。
使われ方：連結の帰納定義の算術的な表示を揃える。 -/
@[reassoc]
lemma tensorPowerSeparation_index (V W : Complex A) {m n : ℕ} (h : m = n) :
    eqToHom (congrArg (power (V ⊗ W)) h) ≫ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerSeparation V W n).hom =
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerSeparation V W m).hom ≫
      (eqToHom (congrArg (power V) h) ⊗ₘ eqToHom (congrArg (power W) h)) := by
  subst n
  simp only [eqToHom_refl, tensorHom_id, id_whiskerRight,
    Category.id_comp, Category.comp_id]

/-- 概要：対の二ブロックを連結して分離する射は各列の連結に一致（BF §3.1）。
方針：前半ブロックを一対ずつ伸ばし、tensorμ の単位・結合則で比較する。
規約：空ブロックと arity の移送を含む。
使われ方：反復評価のブロック連結公式を証明する。 -/
@[reassoc]
lemma tensorPowerSeparation_append (V W : Complex A) (m n : ℕ) :
    (appendIso (V ⊗ W) m n).hom ≫ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerSeparation V W (m + n)).hom =
    ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerSeparation V W m).hom ⊗ₘ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerSeparation V W n).hom) ≫
      tensorμ (power V m) (power W m) (power V n) (power W n) ≫
      ((appendIso V m n).hom ⊗ₘ (appendIso W m n).hom) := by
  induction m with
  | zero =>
    apply (cancel_mono (eqToHom (congrArg (power V) (Nat.zero_add n)) ⊗ₘ
      eqToHom (congrArg (power W) (Nat.zero_add n)))).1
    simp only [Category.assoc]
    rw [← _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerSeparation_index V W (Nat.zero_add n), ← Category.assoc,
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerAppend_zero_transport]
    simp only [tensorHom_comp_tensorHom, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerAppend_zero_transport]
    exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorSeparation_appendZero (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerSeparation V W n).hom
  | succ m ih =>
    apply (cancel_mono (eqToHom (congrArg (power V) (Nat.succ_add m n)) ⊗ₘ
      eqToHom (congrArg (power W) (Nat.succ_add m n)))).1
    simp only [Category.assoc]
    rw [← _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerSeparation_index V W (Nat.succ_add m n), ← Category.assoc,
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerAppend_succ_transport]
    simp only [Category.assoc, tensorHom_comp_tensorHom, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerAppend_succ_transport]
    change (α_ (V ⊗ W) (power (V ⊗ W) m) (power (V ⊗ W) n)).hom ≫
      ((V ⊗ W) ◁ (appendIso (V ⊗ W) m n).hom) ≫
      ((V ⊗ W) ◁ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerSeparation V W (m + n)).hom) ≫
      tensorμ V W (power V (m + n)) (power W (m + n)) = _
    rw [← whiskerLeft_comp_assoc, ih]
    exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorSeparation_appendStep (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerSeparation V W m).hom
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerSeparation V W n).hom (appendIso V m n).hom (appendIso W m n).hom

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads
