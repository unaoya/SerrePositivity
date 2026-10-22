module

public import SerrePositivity.KST.LocalizingInvariants.ProLevelwiseInverse

/-!
概要：元の可換正方形に沿って、指定した eventual 逆の両三角形を移送する。
方針：右の比較で前合成し、左の比較の指定逆で後合成して自然性を使う。
規約：逆射を新たに選び直さない。使われ方：実 dg roof の正方形移送。
-/

@[expose] public section
noncomputable section
universe u v
open CategoryTheory
namespace SerrePositivity.KST.LocalizingInvariants.TowerDiagram
open ProExcision
variable {C : Type u} [Category.{v} C] {X Y X' Y' : Tower C}

lemma inverse_square_triangles (f : LevelHom X Y) (g : LevelHom X' Y')
    (a : LevelHom X X') (b : LevelHom Y Y') (hs : f.comp b = a.comp g)
    {i m : ℕ} (hi : i ≤ m) (r : Y'.obj m ⟶ X'.obj i)
    (hr : g.app m ≫ r = X'.transition hi) (rh : r ≫ g.app i = Y'.transition hi)
    (q : X'.obj i ⟶ X.obj i) (hq : a.app i ≫ q = 𝟙 _) (qh : q ≫ a.app i = 𝟙 _)
    [Mono (b.app i)] :
    f.app m ≫ ((b.app m ≫ r) ≫ q) = X.transition hi ∧
      ((b.app m ≫ r) ≫ q) ≫ f.app i = Y.transition hi := by
  have hs' (j : ℕ) : f.app j ≫ b.app j = a.app j ≫ g.app j :=
    congrArg (fun t => t.app j) hs
  constructor
  · calc
      _ = (a.app m ≫ (g.app m ≫ r)) ≫ q := by
        simp only [← Category.assoc, hs']
      _ = (a.app m ≫ X'.transition hi) ≫ q := by rw [hr]
      _ = (X.transition hi ≫ a.app i) ≫ q := by rw [a.naturality hi]
      _ = _ := by rw [Category.assoc, hq, Category.comp_id]
  · apply (cancel_mono (b.app i)).1
    calc
      _ = (b.app m ≫ r) ≫ (q ≫ (a.app i ≫ g.app i)) := by
        simp only [Category.assoc, hs']
      _ = (b.app m ≫ r) ≫ g.app i := by
        rw [← Category.assoc q, qh, Category.id_comp]
      _ = b.app m ≫ Y'.transition hi := by rw [Category.assoc, rh]
      _ = _ := (b.naturality hi).symm

end SerrePositivity.KST.LocalizingInvariants.TowerDiagram
