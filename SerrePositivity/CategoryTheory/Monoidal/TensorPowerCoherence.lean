module

public import SerrePositivity.CategoryTheory.Monoidal.TensorPowers
public import Mathlib.Tactic.CategoryTheory.Monoidal.Basic

/-!
# 反復テンソルの連結と結合・単位の整合性

次数の等式による移送を含めて、連結同型の単位と結合を比較する。
置換作用や球面を仮定しない一般のモノイダル圏の結果。
-/

@[expose] public section

universe v u

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.TensorPowers

open CategoryTheory CategoryTheory.MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- 連結の左単位は左unitorと次数の移送。 -/
lemma appendIso_zero_left (X : C) (n : ℕ) :
    (appendIso X 0 n).hom =
      (λ_ (power X n)).hom ≫ eqToHom (congrArg (power X) (Nat.zero_add n).symm) := rfl

/-- 連結の右単位は右unitor。 -/
lemma appendIso_zero_right (X : C) (n : ℕ) :
    (appendIso X n 0).hom = (ρ_ (power X n)).hom := by
  induction n with
  | zero =>
    simp only [appendIso, power, Iso.trans_hom, eqToIso.hom, eqToHom_refl, Category.comp_id]
    monoidal
  | succ n ih =>
    simp only [appendIso, power, Iso.trans_hom, eqToIso.hom, eqToHom_refl,
      whiskerLeftIso_hom, Category.comp_id]
    rw [ih]
    monoidal

/-- 一因子を付けた次数の移送は左whiskerと一致する。 -/
lemma power_index_succ (X : C) {m n : ℕ} (h : m = n) :
    eqToHom (congrArg (power X) (congrArg Nat.succ h)) =
      X ◁ eqToHom (congrArg (power X) h) := by
  subst n
  simp [power]

/-- 連結の第一次数の移送は連結同型と両立する。 -/
@[reassoc] lemma appendIso_index_left (X : C) {l l' : ℕ} (h : l = l') (m : ℕ) :
    (eqToHom (congrArg (power X) h) ▷ power X m) ≫ (appendIso X l' m).hom =
      (appendIso X l m).hom ≫ eqToHom (congrArg (power X) (congrArg (· + m) h)) := by
  subst l'
  simp

/-- 連結の第二次数の移送は連結同型と両立する。 -/
@[reassoc] lemma appendIso_index_right (X : C) (l : ℕ) {m m' : ℕ} (h : m = m') :
    (power X l ◁ eqToHom (congrArg (power X) h)) ≫ (appendIso X l m').hom =
      (appendIso X l m).hom ≫ eqToHom (congrArg (power X) (congrArg (l + ·) h)) := by
  subst m'
  simp

/-- 後続次数の三つの移送は、帰納段階の移送と一致する。 -/
lemma append_associativity_succ_cast (X : C) (l m n : ℕ) :
    eqToHom (congrArg (power X) (Nat.succ_add (l + m) n).symm) ≫
        eqToHom (congrArg (power X) (congrArg (· + n) (Nat.succ_add l m).symm)) ≫
        eqToHom (congrArg (power X) (Nat.add_assoc (l + 1) m n)) =
      (X ◁ eqToHom (congrArg (power X) (Nat.add_assoc l m n))) ≫
        eqToHom (congrArg (power X) (Nat.succ_add l (m + n)).symm) := by
  rw [whiskerLeft_eqToHom]
  simp only [eqToHom_trans]

/-- 三つの次数の連結は結合子と両立する。 -/
lemma appendIso_associativity (X : C) (l m n : ℕ) :
    ((appendIso X l m).hom ▷ power X n) ≫ (appendIso X (l + m) n).hom ≫
        eqToHom (congrArg (power X) (Nat.add_assoc l m n)) =
      (α_ (power X l) (power X m) (power X n)).hom ≫
        (power X l ◁ (appendIso X m n).hom) ≫ (appendIso X l (m + n)).hom := by
  induction l with
  | zero =>
    simp only [appendIso, power, Iso.trans_hom, eqToIso.hom, comp_whiskerRight,
      Category.assoc]
    erw [appendIso_index_left_assoc X (Nat.zero_add m).symm n, leftUnitor_whiskerRight]
    simp only [Category.assoc]
    rw [← leftUnitor_naturality_assoc]
    simp only [eqToHom_trans]
  | succ l ih =>
    simp only [appendIso, power, Iso.trans_hom, eqToIso.hom, whiskerLeftIso_hom,
      comp_whiskerRight, Category.assoc]
    erw [appendIso_index_left_assoc X (Nat.succ_add l m).symm n]
    simp only [appendIso, Iso.trans_hom, eqToIso.hom, whiskerLeftIso_hom, Category.assoc]
    erw [append_associativity_succ_cast X l m n]
    rw [associator_naturality_middle_assoc]
    simp only [← whiskerLeft_comp_assoc]
    rw [ih]
    simp only [whiskerLeft_comp, Category.assoc]
    rw [pentagon_assoc, ← associator_naturality_right_assoc]

/-- 第1段を左に連結する同型は、右単位子と次数の移送。 -/
lemma appendIso_one_left (X : C) (n : ℕ) :
    (appendIso X 1 n).hom = (ρ_ X).hom ▷ power X n ≫
      eqToHom (congrArg (power X) (Nat.one_add n).symm) := by
  simp only [appendIso, power, Iso.trans_hom, whiskerLeftIso_hom, eqToIso.hom,
    whiskerLeft_comp, whiskerLeft_eqToHom, Category.assoc, eqToHom_trans]
  erw [triangle_assoc]
end SerrePositivity.TensorPowers
