module

public import SerrePositivity.KST.LocalizingInvariants.ProInverseAfter

/-!
概要：同じ元のレベル射の左逆三角形を持つ二射は、後続段で一致する。
方針：両始域以降の共通段を取り、元の pro 逆の右三角形で元の射の像へ入れる。
規約：一般 pro 圏を入力しない。使われ方：平方零逆の底と元の roof の底の一致。
-/

@[expose] public section
noncomputable section
universe u v
open CategoryTheory
namespace SerrePositivity.KST.LocalizingInvariants.TowerDiagram
open ProExcision
variable {C : Type u} [Category.{v} C] {X Y : Tower C} (f : LevelHom X Y)

lemma inverse_left_eventually_unique (hf : IsProIso f) {i m l : ℕ}
    (hi : i ≤ m) (hj : i ≤ l) (r : Y.obj m ⟶ X.obj i) (s : Y.obj l ⟶ X.obj i)
    (hr : f.app m ≫ r = X.transition hi) (hs : f.app l ≫ s = X.transition hj) :
    ∃ k, ∃ hm : m ≤ k, ∃ hl : l ≤ k, Y.transition hm ≫ r = Y.transition hl ≫ s := by
  let q := max m l
  have hm : m ≤ q := le_max_left _ _
  have hl : l ≤ q := le_max_right _ _
  obtain ⟨k, hk, b, hb, bh⟩ := hf q
  have h₁ : f.app q ≫ (Y.transition hm ≫ r) = X.transition (hi.trans hm) := by
    rw [← Category.assoc, ← f.naturality hm, Category.assoc, hr, X.transition_comp]
  have h₂ : f.app q ≫ (Y.transition hl ≫ s) = X.transition (hj.trans hl) := by
    rw [← Category.assoc, ← f.naturality hl, Category.assoc, hs, X.transition_comp]
  refine ⟨k, hm.trans hk, hl.trans hk, ?_⟩
  calc
    _ = (Y.transition hk ≫ Y.transition hm) ≫ r := by rw [Y.transition_comp]
    _ = b ≫ (f.app q ≫ (Y.transition hm ≫ r)) := by rw [← Category.assoc, bh, Category.assoc]
    _ = b ≫ X.transition (hi.trans hm) := congrArg (fun t => b ≫ t) h₁
    _ = b ≫ (f.app q ≫ (Y.transition hl ≫ s)) :=
      congrArg (fun t => b ≫ t) h₂.symm
    _ = (Y.transition hk ≫ Y.transition hl) ≫ s := by rw [← Category.assoc, bh, Category.assoc]
    _ = _ := by rw [Y.transition_comp]

lemma inverse_span_left {S P U V W : C} (a : S ⟶ U) (l : S ⟶ P)
    (d : P ⟶ V) (b : P ⟶ W) (g : U ⟶ V) (t : U ⟶ W)
    [Epi a] [IsIso d] (hl : l ≫ d = a ≫ g) (hb : l ≫ b = a ≫ t) :
    g ≫ (inv d ≫ b) = t := by
  apply (cancel_epi a).1
  calc
    _ = (l ≫ d) ≫ (inv d ≫ b) := (Category.assoc _ _ _).symm.trans
      (congrArg (fun z => z ≫ (inv d ≫ b)) hl.symm)
    _ = l ≫ b := by simp only [Category.assoc, IsIso.hom_inv_id_assoc]
    _ = _ := hb

end SerrePositivity.KST.LocalizingInvariants.TowerDiagram
