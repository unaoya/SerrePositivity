module

public import SerrePositivity.KST.LocalizingInvariants.ProTowerNatMap

/-!
概要：成分が可逆な実レベル射の逆と、元の合成の pro 同型からの右側判定を供給する。
方針：元の成分の逆射を自然性の四角形で比較し、元の合成を正確に回収する。
規約：一般 pro 圏を構成しない。使われ方：像因子分解の低次数の標的側判定。
-/

@[expose] public section
noncomputable section
universe u v
open CategoryTheory
namespace SerrePositivity.KST.LocalizingInvariants.TowerDiagram
open ProExcision
variable {C : Type u} [Category.{v} C] {X Y Z : Tower C} (f : LevelHom X Y)
  [∀ n, IsIso (f.app n)]

def levelInverse : LevelHom Y X where
  app n := inv (f.app n)
  naturality {m n} h := by
    apply (cancel_epi (f.app m)).1
    calc
      _ = X.transition h := by
        rw [← Category.assoc, ← f.naturality, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
      _ = _ := by rw [← Category.assoc, IsIso.hom_inv_id, Category.id_comp]

lemma inverse_comp (g : LevelHom Y Z) : (levelInverse f).comp (f.comp g) = g := by
  apply ProSpectrum.levelHom_ext
  intro n
  change inv (f.app n) ≫ (f.app n ≫ g.app n) = g.app n
  rw [← Category.assoc, IsIso.inv_hom_id, Category.id_comp]

lemma proIso_of_comp_left_levelwiseIso (g : LevelHom Y Z) (h : IsProIso (f.comp g)) :
    IsProIso g := by
  have : ∀ n, IsIso ((levelInverse f).app n) := fun n => by
    change IsIso (inv (f.app n))
    infer_instance
  have hi : IsProIso (levelInverse f) := isProIso_of_levelwiseIso _
  have hc := hi.comp h
  rw [inverse_comp] at hc
  exact hc

lemma comp_inverse {W : Tower C} (a : LevelHom W X) :
    (a.comp f).comp (levelInverse f) = a := by
  apply ProSpectrum.levelHom_ext
  intro n
  change (a.app n ≫ f.app n) ≫ inv (f.app n) = a.app n
  rw [Category.assoc, IsIso.hom_inv_id, Category.comp_id]

lemma proIso_of_comp_right_levelwiseIso {W : Tower C} (a : LevelHom W X)
    (h : IsProIso (a.comp f)) : IsProIso a := by
  have : ∀ n, IsIso ((levelInverse f).app n) := fun n => by
    change IsIso (inv (f.app n))
    infer_instance
  have hi : IsProIso (levelInverse f) := isProIso_of_levelwiseIso _
  have hc := h.comp hi
  rw [comp_inverse] at hc
  exact hc

omit [∀ n, IsIso (f.app n)] in
lemma proIso_of_square {X' Y' : Tower C} (g : LevelHom X' Y') (a : LevelHom X X')
    (b : LevelHom Y Y') [∀ n, IsIso (a.app n)] [∀ n, IsIso (b.app n)]
    (hs : f.comp b = a.comp g) (hf : IsProIso f) : IsProIso g := by
  have hb : IsProIso b := isProIso_of_levelwiseIso _
  have hc := hf.comp hb
  rw [hs] at hc
  exact proIso_of_comp_left_levelwiseIso a g hc

end SerrePositivity.KST.LocalizingInvariants.TowerDiagram
