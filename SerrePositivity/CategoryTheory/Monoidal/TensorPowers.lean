module

public import Mathlib.CategoryTheory.Monoidal.Functor

/-!
# 反復テンソルと次数の連結

右に括った反復テンソルを定義し、対象の射から各次数の射を得る。
結合子と単位により、二つの反復テンソルを和次数へまとめる同型を構成する。
置換作用と対称列としての関手性は、この基盤の上で別に証明する。
-/

@[expose] public section

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
