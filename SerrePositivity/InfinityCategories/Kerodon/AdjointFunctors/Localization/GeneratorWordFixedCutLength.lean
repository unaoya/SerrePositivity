module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFixedCut
public import Mathlib.Combinatorics.Quiver.Cast

/-!
# 元の一文字の射列の切断の前後の長さと恒等移送

概要：元の長さ一の列の FixedCut の前後は長さ零であり、元の端点等式の移送である。
方針：元の射列の因子化の長さを取り、長さ零の射列を場合分けする。
規約：元の恒等文字と長さ零の射列を区別する。
使われ方：貼り戻し後の prefix・残りの元の点の回収。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory

variable {C : Type u} [Category.{v} C]

lemma path_length_comp {A B D : Paths C} (p : A ⟶ B) (q : B ⟶ D) :
    (p ≫ q).length = p.length + q.length := Quiver.Path.length_comp p q

lemma path_length_eqToHom {A B : Paths C} (h : A = B) : (eqToHom h).length = 0 := by
  cases h
  rfl

lemma path_length_transport {A A' B B' : Paths C} (hA : A' = A) (hB : B = B') (p : A ⟶ B) :
    (eqToHom hA ≫ p ≫ eqToHom hB).length = p.length := by
  cases hA
  cases hB
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

lemma path_eqToHom_of_length_zero {A B : Paths C} (p : A ⟶ B) (hp : p.length = 0) :
    ∃ h : A = B, p = eqToHom h := by
  cases p with
  | nil => exact ⟨rfl, rfl⟩
  | cons p f => simp only [Quiver.Path.length_cons, Nat.add_one_ne_zero] at hp

namespace FixedCut
variable (W : MorphismProperty C) {g : Quiver.Total C} {A B : Paths C} {p : A ⟶ B}
  (P : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FixedCut W g p)

lemma length_factorization : p.length = P.left.length + (1 + P.right.length) := by
  have h := congrArg Quiver.Path.length P.factorization
  simpa only [Quiver.Path.length_comp, Quiver.Path.length_toPath] using h

lemma left_length_of_one (hp : p.length = 1) : P.left.length = 0 := by
  have h := length_factorization W P
  omega

lemma right_length_of_one (hp : p.length = 1) : P.right.length = 0 := by
  have h := length_factorization W P
  omega

lemma left_eqToHom_of_one (hp : p.length = 1) :
    ∃ h : A = (show Paths C from g.left), P.left = eqToHom h :=
  path_eqToHom_of_length_zero P.left (left_length_of_one W P hp)

lemma right_eqToHom_of_one (hp : p.length = 1) :
    ∃ h : (show Paths C from g.right) = B, P.right = eqToHom h :=
  path_eqToHom_of_length_zero P.right (right_length_of_one W P hp)

end FixedCut
end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
