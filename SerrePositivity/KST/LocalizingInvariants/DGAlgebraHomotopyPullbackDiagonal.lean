module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraHomotopyPullbackProBase
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraHomotopyPullbackMapCocone

/-!
概要：自己 cospan の実対角を、元の二脚と定数経路を保つ自然な代数射として構成する。
方針：両脚を恒等射とする実 lift を用い、三成分で自然性を検証する。
規約：経路模型を通常 pullback と同一視しない。使われ方：二切断逆の対角反映。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits CochainComplex HomComplex
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.HomotopyPullbackModel
variable (R : Type u) [CommRing R] {A B : Mon (Complex R)} (f : A ⟶ B)

def diagonal : A ⟶ algebra R f f :=
  lift R f f (𝟙 A) (𝟙 A)
    ⟨f ≫ Path.diagonal R B, by simp [Path.diagonal_source],
      by simp [Path.diagonal_target]⟩

lemma diagonal_left : diagonal R f ≫ left R f f = 𝟙 A := lift_left R _ _ _ _ _

lemma diagonal_right : diagonal R f ≫ right R f f = 𝟙 A := lift_right R _ _ _ _ _

lemma diagonal_path : diagonal R f ≫ path R f f = f ≫ Path.diagonal R B :=
  lift_path R _ _ _ _ _

lemma diagonal_pair : (diagonal R f).hom ≫ pairHom R f f = biprod.lift (𝟙 _) (𝟙 _) := by
  apply biprod.hom_ext
  · rw [Category.assoc, pairHom_fst, biprod.lift_fst]
    exact congrArg Mon.Hom.hom (diagonal_left R f)
  · rw [Category.assoc, pairHom_snd, biprod.lift_snd]
    exact congrArg Mon.Hom.hom (diagonal_right R f)

lemma diagonal_primitive :
    (Cochain.ofHom (diagonal R f).hom).comp (primitive R f f) (zero_add (-1)) = 0 := by
  rw [primitive, ← Cochain.comp_assoc_of_first_is_zero_cochain, ← Cochain.ofHom_comp]
  have h := congrArg Mon.Hom.hom (diagonal_path R f)
  change (diagonal R f).hom ≫ (path R f f).hom = f.hom ≫ Path.diagonalHom R B at h
  rw [h, Cochain.ofHom_comp, Cochain.comp_assoc_of_first_is_zero_cochain,
    Path.diagonalHom_primitive, Cochain.comp_zero]

lemma diagonal_naturality {C D : Mon (Complex R)} (g : C ⟶ D) (a : A ⟶ C) (b : B ⟶ D)
    (h : a ≫ g = f ≫ b) :
    diagonal R f ≫ map R f f g g a b a h h = a ≫ diagonal R g := by
  apply hom_ext R g g
  · rw [Category.assoc, map_left, ← Category.assoc, diagonal_left,
      Category.id_comp, Category.assoc, diagonal_left, Category.comp_id]
  · rw [Category.assoc, map_right, ← Category.assoc, diagonal_right,
      Category.id_comp, Category.assoc, diagonal_right, Category.comp_id]
  · rw [Category.assoc, map_path, ← Category.assoc, diagonal_path,
      Category.assoc, Path.diagonal_naturality, ← Category.assoc, ← h,
      Category.assoc, Category.assoc a, diagonal_path]

variable {X Y : ProExcision.Tower (Mon (Complex R))} (F : ProExcision.LevelHom X Y)

def diagonalHom : ProExcision.LevelHom X (modelTower R F F) where
  app i := diagonal R (F.app i)
  naturality h := (diagonal_naturality R (F.app _) (F.app _)
    (X.transition h) (Y.transition h) (F.naturality h)).symm

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.HomotopyPullbackModel
