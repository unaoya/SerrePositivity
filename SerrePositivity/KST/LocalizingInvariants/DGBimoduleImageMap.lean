module

public import SerrePositivity.KST.LocalizingInvariants.DGBimoduleImage
public import SerrePositivity.KST.LocalizingInvariants.BimoduleRestriction

/-!
概要：底変更を含む実双加群の可換正方形から、元の係数像の実双加群射を構成する。
方針：複体圏の像関手の射を使い、元の包含の単射性で左右作用の保存を証明する。
規約：元の包含・射影を保持。使われ方：Postnikov 像拡大の正方形に沿う作用。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGBimoduleImage
variable {R : Type u} [CommRing R] {A A' : Mon (Complex R)}
  {M N : Bimod A A} {M' N' : Bimod A' A'} (q : A ⟶ A') (f : M ⟶ N) (f' : M' ⟶ N')
  (a : M ⟶ bimoduleRestrict q M') (b : N ⟶ bimoduleRestrict q N')
  (h : f.hom ≫ b.hom = a.hom ≫ f'.hom)

def mapSquare : Arrow.mk f.hom ⟶ Arrow.mk f'.hom := Arrow.homMk' a.hom b.hom h.symm

def mapHom : (obj f).X ⟶ (obj f').X := image.map (mapSquare q f f' a b h)

lemma mapHom_inclusion : mapHom q f f' a b h ≫ (inclusion f').hom =
    (inclusion f).hom ≫ b.hom := image.map_ι (mapSquare q f f' a b h)

lemma mapHom_projection : (projection f).hom ≫ mapHom q f f' a b h =
    a.hom ≫ (projection f').hom := image.factor_map (mapSquare q f f' a b h)

lemma mapHom_left : (obj f).actLeft ≫ mapHom q f f' a b h =
    (q.hom ⊗ₘ mapHom q f f' a b h) ≫ (obj f').actLeft := by
  have := inclusion_mono f'
  have hi : (obj f).actLeft ≫ (inclusion f).hom = (A.X ◁ (inclusion f).hom) ≫ N.actLeft :=
    (inclusion f).left_act_hom
  have hi' : (obj f').actLeft ≫ (inclusion f').hom =
      (A'.X ◁ (inclusion f').hom) ≫ N'.actLeft := (inclusion f').left_act_hom
  have hb : N.actLeft ≫ b.hom = (q.hom ⊗ₘ b.hom) ≫ N'.actLeft := by
    rw [tensorHom_def']
    exact b.left_act_hom
  apply (cancel_mono (inclusion f').hom).1
  rw [Category.assoc, mapHom_inclusion, ← Category.assoc, hi, Category.assoc, hb,
    Category.assoc (q.hom ⊗ₘ mapHom q f f' a b h), hi']
  simp only [← id_tensorHom, tensorHom_comp_tensorHom_assoc,
    Category.id_comp, Category.comp_id, mapHom_inclusion]

lemma mapHom_right : (obj f).actRight ≫ mapHom q f f' a b h =
    (mapHom q f f' a b h ⊗ₘ q.hom) ≫ (obj f').actRight := by
  have := inclusion_mono f'
  have hi : (obj f).actRight ≫ (inclusion f).hom =
      ((inclusion f).hom ▷ A.X) ≫ N.actRight := (inclusion f).right_act_hom
  have hi' : (obj f').actRight ≫ (inclusion f').hom =
      ((inclusion f').hom ▷ A'.X) ≫ N'.actRight := (inclusion f').right_act_hom
  have hb : N.actRight ≫ b.hom = (b.hom ⊗ₘ q.hom) ≫ N'.actRight := by
    rw [tensorHom_def]
    exact b.right_act_hom
  apply (cancel_mono (inclusion f').hom).1
  rw [Category.assoc, mapHom_inclusion, ← Category.assoc, hi, Category.assoc, hb,
    Category.assoc (mapHom q f f' a b h ⊗ₘ q.hom), hi']
  simp only [← tensorHom_id, tensorHom_comp_tensorHom_assoc,
    Category.id_comp, Category.comp_id, mapHom_inclusion]

def map : obj f ⟶ bimoduleRestrict q (obj f') where
  hom := mapHom q f f' a b h
  left_act_hom := by
    change _ = (_ ◁ _) ≫ (_ ▷ _) ≫ _
    rw [← tensorHom_def'_assoc]
    exact mapHom_left q f f' a b h
  right_act_hom := by
    change _ = (_ ▷ _) ≫ (_ ◁ _) ≫ _
    rw [← tensorHom_def_assoc]
    exact mapHom_right q f f' a b h

end SerrePositivity.KST.LocalizingInvariants.DGBimoduleImage
