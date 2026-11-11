module

public import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
概要：終対象上の厳密な pullback を、同じ二射影を持つ直積に同定する。
方針：終対象への可換条件の一意性で直積からの逆射を作る。
規約：単体集合の充填性は要求しない。
使われ方：一次元境界の元の native Hom と分類先 Hom を両端へ分解する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
namespace SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Pullbacks
variable {A B C D : SSet.{u}} {f : A ⟶ B} {g : A ⟶ C} {r : B ⟶ D} {s : C ⟶ D}
  (h : IsPullback f g r s) (hD : IsTerminal D)

/-- 同じ二つの射影を保つ、終対象上の pullback と直積の同型。 -/
def pullbackTerminalProductIso : A ≅ B ⊗ C where
  hom := lift f g
  inv := h.lift (fst B C) (snd B C) (hD.hom_ext _ _)
  hom_inv_id := by
    apply h.hom_ext
    · rw [Category.assoc, h.lift_fst, lift_fst, Category.id_comp]
    · rw [Category.assoc, h.lift_snd, lift_snd, Category.id_comp]
  inv_hom_id := by
    apply CartesianMonoidalCategory.hom_ext
    · rw [Category.assoc, lift_fst, h.lift_fst, Category.id_comp]
    · rw [Category.assoc, lift_snd, h.lift_snd, Category.id_comp]

/-- 同じ同型の第一射影は元の第一射影。 -/
lemma pullbackTerminalProductIso_hom_fst :
    (pullbackTerminalProductIso h hD).hom ≫ fst B C = f := lift_fst _ _

/-- 同じ同型の第二射影は元の第二射影。 -/
lemma pullbackTerminalProductIso_hom_snd :
    (pullbackTerminalProductIso h hD).hom ≫ snd B C = g := lift_snd _ _

end SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Pullbacks
