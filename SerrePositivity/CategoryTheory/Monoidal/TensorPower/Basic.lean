module

public import Mathlib.CategoryTheory.Monoidal.Functor
public import Mathlib.Tactic.CategoryTheory.Monoidal.Basic

/-!
# Monoidal.TensorPower.Basic

## 概要
関連する圏論の構成と補題をまとめる。各構成の詳細は以下の元モジュールの説明を参照。

## 方針
元の宣言と証明を保持し、依存順に section を分けて配置する。

## 規約
公開宣言名・名前空間・宇宙変数の意味を変更しない。元の module docstring は各節に保存する。

## 使われ方
旧モジュールの利用元は `SerrePositivity.CategoryTheory.Monoidal.TensorPower.Basic` を直接 import する。
-/

/-! ## TensorPowers（旧 SerrePositivity/CategoryTheory/Monoidal/TensorPowers.lean） -/

/-!
# 反復テンソルと次数の連結

右に括った反復テンソルを定義し、対象の射から各次数の射を得る。
結合子と単位により、二つの反復テンソルを和次数へまとめる同型を構成する。
置換作用と対称列としての関手性は、この基盤の上で別に証明する。
-/

@[expose] public section TensorPowers
universe v u

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.TensorPowers

open CategoryTheory CategoryTheory.MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- 第0段はテンソル単位とする、右に括った反復テンソル。 -/
def power (X : C) : ℕ → C
  | 0 => 𝟙_ C
  | n + 1 => X ⊗ power X n

/-- 対象の射が反復テンソルに誘導する射。 -/
def map {X Y : C} (f : X ⟶ Y) : ∀ n, power X n ⟶ power Y n
  | 0 => 𝟙 (𝟙_ C)
  | n + 1 => f ⊗ₘ map f n

@[simp] lemma map_id (X : C) (n : ℕ) : map (𝟙 X) n = 𝟙 (power X n) := by
  induction n with
  | zero => rfl
  | succ n ih => simp [map, ih, power]

@[simp] lemma map_comp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (n : ℕ) :
    map (f ≫ g) n = map f n ≫ map g n := by
  induction n with
  | zero => exact (Category.id_comp _).symm
  | succ n ih =>
    change (f ≫ g) ⊗ₘ map (f ≫ g) n = (f ⊗ₘ map f n) ≫ (g ⊗ₘ map g n)
    rw [ih]
    exact (tensorHom_comp_tensorHom f (map f n) g (map g n)).symm

/-- 各次数の反復テンソルは基礎圏の自己関手。 -/
def powerFunctor (n : ℕ) : C ⥤ C where
  obj X := power X n
  map f := map f n
  map_id X := map_id X n
  map_comp f g := map_comp f g n

/-- 二つの反復テンソルを、和次数の反復テンソルへ連結する同型。 -/
def appendIso (X : C) : ∀ m n, power X m ⊗ power X n ≅ power X (m + n)
  | 0, n => (λ_ (power X n)) ≪≫ eqToIso (congrArg (power X) (Nat.zero_add n).symm)
  | m + 1, n =>
    (α_ X (power X m) (power X n)) ≪≫ whiskerLeftIso X (appendIso X m n) ≪≫
      eqToIso (congrArg (power X) (Nat.succ_add m n).symm)

/-- 次数の等式による移送は、対象の射から誘導した射と両立する。 -/
@[reassoc] lemma map_index_eq {X Y : C} (f : X ⟶ Y) {m n : ℕ} (h : m = n) :
    map f m ≫ eqToHom (congrArg (power Y) h) =
      eqToHom (congrArg (power X) h) ≫ map f n := by
  subst n
  simp

/-- 和次数への連結は対象の射に関して自然。 -/
lemma appendIso_naturality {X Y : C} (f : X ⟶ Y) (m n : ℕ) :
    (map f m ⊗ₘ map f n) ≫ (appendIso Y m n).hom =
      (appendIso X m n).hom ≫ map f (m + n) := by
  induction m with
  | zero =>
    simp only [appendIso, power, map, Iso.trans_hom, eqToIso.hom, id_tensorHom, Category.assoc]
    rw [leftUnitor_naturality_assoc, map_index_eq f (Nat.zero_add n).symm]
  | succ m ih =>
    have h : (f ⊗ₘ (map f m ⊗ₘ map f n)) ≫ (Y ◁ (appendIso Y m n).hom) =
        (X ◁ (appendIso X m n).hom) ≫ (f ⊗ₘ map f (m + n)) := by
      simp only [← id_tensorHom, tensorHom_comp_tensorHom, Category.comp_id, Category.id_comp]
      exact congrArg (fun k ↦ f ⊗ₘ k) ih
    simp only [appendIso, power, map, Iso.trans_hom, eqToIso.hom, whiskerLeftIso_hom,
      Category.assoc]
    rw [associator_naturality_assoc, ← Category.assoc _ _ (eqToHom _), h]
    simp only [Category.assoc]
    rw [show f ⊗ₘ map f (m + n) = map f ((m + n) + 1) from rfl,
      map_index_eq f (Nat.succ_add m n).symm]

/-- 反復テンソルの第1段と元の対象の比較。 -/
def oneIso (X : C) : power X 1 ≅ X := ρ_ X

/-- 第1段の比較は対象に関して自然。 -/
lemma oneIso_naturality {X Y : C} (f : X ⟶ Y) :
    map f 1 ≫ (oneIso Y).hom = (oneIso X).hom ≫ f := by
  change (f ⊗ₘ 𝟙 (𝟙_ C)) ≫ (ρ_ Y).hom = (ρ_ X).hom ≫ f
  rw [tensorHom_id]
  exact rightUnitor_naturality f

/-- 第1段の反復テンソル関手は恒等関手と自然同型。 -/
def oneNatIso : powerFunctor (C := C) 1 ≅ 𝟭 C :=
  NatIso.ofComponents oneIso (fun f ↦ oneIso_naturality f)

end SerrePositivity.TensorPowers
end

end TensorPowers

/-! ## TensorPowerCoherence（旧 SerrePositivity/CategoryTheory/Monoidal/TensorPowerCoherence.lean） -/

/-!
# 反復テンソルの連結と結合・単位の整合性

次数の等式による移送を含めて、連結同型の単位と結合を比較する。
置換作用や球面を仮定しない一般のモノイダル圏の結果。
-/

@[expose] public section TensorPowerCoherence
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
end

end TensorPowerCoherence
