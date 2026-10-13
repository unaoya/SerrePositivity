module

public import Mathlib.CategoryTheory.Core
public import Mathlib.CategoryTheory.FintypeCat
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.GroupTheory.Perm.Basic

/-!
# 有限集合と全単射の小さい骨格

Mathlib の有限集合の標準骨格の core を使う小さい亜群。
対象は有限の濃度、射はその標準有限集合の全単射であり、一般の写像を含めない。
射と `Fin n` の同値の対応を明示して、置換作用の規約を固定する。
対称列以外にも使える共通の圏論基盤。
-/

@[expose] public section

namespace SerrePositivity

open CategoryTheory

/-- 有限集合の標準骨格における全単射の圏。 -/
abbrev FiniteBijection := Core FintypeCat.Skeleton.{0}

namespace FiniteBijection

/-- n 元の標準有限集合。 -/
def of (n : ℕ) : FiniteBijection := ⟨FintypeCat.Skeleton.mk n⟩

/-- 対象の濃度。 -/
def card (X : FiniteBijection) : ℕ := (Core.of X).len

@[simp] lemma card_of (n : ℕ) : card (of n) = n := rfl

@[simp] lemma of_card (X : FiniteBijection) : of (card X) = X := by
  cases X with | mk X => cases X; rfl

/-- 全単射を core の射へ戻す。 -/
def homOfEquiv {X Y : FiniteBijection} (e : Fin (card X) ≃ Fin (card Y)) : X ⟶ Y :=
  ⟨{ hom := fun x ↦ ⟨e x.down⟩
     inv := fun y ↦ ⟨e.symm y.down⟩
     hom_inv_id := by funext x; apply ULift.ext; exact e.symm_apply_apply x.down
     inv_hom_id := by funext y; apply ULift.ext; exact e.apply_symm_apply y.down }⟩

/-- core の射を標準有限集合の全単射として読む。 -/
def equivOfHom {X Y : FiniteBijection} (f : X ⟶ Y) : Fin (card X) ≃ Fin (card Y) where
  toFun x := (f.iso.hom ⟨x⟩).down
  invFun y := (f.iso.inv ⟨y⟩).down
  left_inv x := by
    have h := congrFun f.iso.hom_inv_id (ULift.up x)
    exact congrArg ULift.down h
  right_inv y := by
    have h := congrFun f.iso.inv_hom_id (ULift.up y)
    exact congrArg ULift.down h

/-- 射は、まさに標準有限集合の全単射。 -/
def homEquiv (X Y : FiniteBijection) : (X ⟶ Y) ≃ (Fin (card X) ≃ Fin (card Y)) where
  toFun := equivOfHom
  invFun := homOfEquiv
  left_inv f := by
    apply Core.hom_ext
    funext x
    rfl
  right_inv e := by ext x; rfl

@[simp] lemma equivOfHom_homOfEquiv {X Y : FiniteBijection}
    (e : Fin (card X) ≃ Fin (card Y)) : equivOfHom (homOfEquiv e) = e :=
  (homEquiv X Y).apply_symm_apply e

@[simp] lemma homOfEquiv_equivOfHom {X Y : FiniteBijection} (f : X ⟶ Y) :
    homOfEquiv (equivOfHom f) = f := (homEquiv X Y).symm_apply_apply f

@[simp] lemma homOfEquiv_refl (X : FiniteBijection) :
    homOfEquiv (Equiv.refl (Fin (card X))) = 𝟙 X := by
  apply Core.hom_ext
  rfl

@[simp] lemma homOfEquiv_trans {X Y Z : FiniteBijection}
    (e : Fin (card X) ≃ Fin (card Y)) (f : Fin (card Y) ≃ Fin (card Z)) :
    homOfEquiv (e.trans f) = homOfEquiv e ≫ homOfEquiv f := by
  apply Core.hom_ext
  rfl

/-- 射があると二つの濃度は等しい。 -/
lemma card_eq_of_hom {X Y : FiniteBijection} (f : X ⟶ Y) : card X = card Y :=
  Fin.equiv_iff_eq.mp ⟨equivOfHom f⟩

/-- 標準対象の自己同型は n 文字の置換。 -/
def permutation (n : ℕ) (σ : Equiv.Perm (Fin n)) : of n ⟶ of n := homOfEquiv σ

@[simp] lemma permutation_one (n : ℕ) : permutation n 1 = 𝟙 (of n) := homOfEquiv_refl _

/-- 群の積と圏の合成では順序が逆になる。作用の乗法則に使う。 -/
lemma permutation_mul (n : ℕ) (σ τ : Equiv.Perm (Fin n)) :
    permutation n (σ * τ) = permutation n τ ≫ permutation n σ :=
  homOfEquiv_trans (X := of n) (Y := of n) (Z := of n) τ σ

/-- 全ての有限集合の全単射圏への標準包含。 -/
def inclusion : FiniteBijection ⥤ Core FintypeCat.{0} := FintypeCat.Skeleton.incl.core

/-- 射があると骨格の対象そのものが等しい。 -/
lemma object_eq_of_hom {X Y : FiniteBijection} (f : X ⟶ Y) : X = Y := by
  rw [← of_card X, ← of_card Y, card_eq_of_hom f]

@[simp] lemma equivOfHom_id (X : FiniteBijection) :
    equivOfHom (𝟙 X) = Equiv.refl (Fin (card X)) := by ext x; rfl

@[simp] lemma equivOfHom_comp {X Y Z : FiniteBijection} (f : X ⟶ Y) (g : Y ⟶ Z) :
    equivOfHom (f ≫ g) = (equivOfHom f).trans (equivOfHom g) := by ext x; rfl

end FiniteBijection
end SerrePositivity
