module

public import SerrePositivity.KST.LocalizingInvariants.ProInverseEventualUniqueness

/-!
概要：可換な元のレベル正方形の両逆は、共通の後続段で正方形と可換になる。
方針：二つの左逆三角形を共通段で比較し、元の右逆三角形を前合成する。
規約：一般 pro 圏や逆の自然性を入力しない。
使われ方：有限 Postnikov 逆の切断間遷移との整合。
-/

@[expose] public section
noncomputable section
universe u v
open CategoryTheory
namespace SerrePositivity.KST.LocalizingInvariants.TowerDiagram
open ProExcision
variable {C : Type u} [Category.{v} C] {X Y X' Y' : Tower C}
  (f : LevelHom X Y) (g : LevelHom X' Y')
  (a : LevelHom X X') (b : LevelHom Y Y')

lemma inverse_square_eventually (hf : IsProIso f)
    (square : f.comp b = a.comp g) {i m l : ℕ} (hi : i ≤ m) (hj : i ≤ l)
    (r : Y.obj m ⟶ X.obj i) (s : Y'.obj l ⟶ X'.obj i)
    (hr : f.app m ≫ r = X.transition hi) (hs : g.app l ≫ s = X'.transition hj) :
    ∃ k, ∃ hm : m ≤ k, ∃ hl : l ≤ k,
      (Y.transition hm ≫ r) ≫ a.app i = (Y.transition hl ≫ b.app l) ≫ s := by
  let q := max m l
  have hm : m ≤ q := le_max_left _ _
  have hl : l ≤ q := le_max_right _ _
  have hsq : f.app l ≫ b.app l = a.app l ≫ g.app l :=
    congrArg (fun t : LevelHom X Y' => t.app l) square
  have h₁ : f.app q ≫ ((Y.transition hm ≫ r) ≫ a.app i) =
      a.app q ≫ X'.transition (hi.trans hm) := by
    calc
      _ = (X.transition hm ≫ f.app m) ≫ (r ≫ a.app i) := by
        rw [← Category.assoc, ← Category.assoc, ← f.naturality hm]
        simp only [Category.assoc]
      _ = (X.transition hm ≫ (f.app m ≫ r)) ≫ a.app i := by
        simp only [Category.assoc]
      _ = (X.transition hm ≫ X.transition hi) ≫ a.app i := by rw [hr]
      _ = X.transition (hi.trans hm) ≫ a.app i := by rw [X.transition_comp]
      _ = _ := a.naturality (hi.trans hm)
  have h₂ : f.app q ≫ ((Y.transition hl ≫ b.app l) ≫ s) =
      a.app q ≫ X'.transition (hj.trans hl) := by
    calc
      _ = (X.transition hl ≫ f.app l) ≫ (b.app l ≫ s) := by
        rw [← Category.assoc, ← Category.assoc, ← f.naturality hl]
        simp only [Category.assoc]
      _ = X.transition hl ≫ (f.app l ≫ b.app l) ≫ s := by
        simp only [Category.assoc]
      _ = X.transition hl ≫ (a.app l ≫ g.app l) ≫ s := by rw [hsq]
      _ = (X.transition hl ≫ a.app l) ≫ (g.app l ≫ s) := by
        simp only [Category.assoc]
      _ = (a.app q ≫ X'.transition hl) ≫ X'.transition hj := by
        rw [a.naturality hl, hs]
      _ = _ := by rw [Category.assoc, X'.transition_comp]
  obtain ⟨k, hk, t, _, ht⟩ := hf q
  refine ⟨k, hm.trans hk, hl.trans hk, ?_⟩
  calc
    _ = t ≫ (f.app q ≫ ((Y.transition hm ≫ r) ≫ a.app i)) := by
      rw [← Category.assoc, ht]
      simp only [← Category.assoc, Y.transition_comp]
    _ = t ≫ (a.app q ≫ X'.transition (hi.trans hm)) := congrArg (fun z => t ≫ z) h₁
    _ = t ≫ (f.app q ≫ ((Y.transition hl ≫ b.app l) ≫ s)) :=
      congrArg (fun z => t ≫ z) h₂.symm
    _ = _ := by
      rw [← Category.assoc, ht]
      simp only [← Category.assoc, Y.transition_comp]

end SerrePositivity.KST.LocalizingInvariants.TowerDiagram
