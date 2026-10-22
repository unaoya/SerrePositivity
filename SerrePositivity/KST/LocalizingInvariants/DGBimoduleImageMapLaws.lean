module

public import SerrePositivity.KST.LocalizingInvariants.DGBimoduleImageMap

/-!
概要：底変更を含む元の像射の一意性と、恒等・合成の厳密な式を供給する。
方針：元の包含の単射性を使い、標的成分の恒等・合成へ帰着する。
規約：合成用の実双加群射を明示し、その underlying 合成式を使う。
使われ方：Postnikov 係数像の正方形の関手則。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGBimoduleImage
variable {R : Type u} [CommRing R] {A A' : Mon (Complex R)}
  {M N : Bimod A A} {M' N' : Bimod A' A'} (q : A ⟶ A') (f : M ⟶ N) (f' : M' ⟶ N')
  (a : M ⟶ bimoduleRestrict q M') (b : N ⟶ bimoduleRestrict q N')
  (h : f.hom ≫ b.hom = a.hom ≫ f'.hom)

lemma mapHom_eq (v : (obj f).X ⟶ (obj f').X)
    (hv : v ≫ (inclusion f').hom = (inclusion f).hom ≫ b.hom) : mapHom q f f' a b h = v := by
  have := inclusion_mono f'
  apply (cancel_mono (inclusion f').hom).1
  exact (mapHom_inclusion q f f' a b h).trans hv.symm

lemma mapHom_identity (q : A ⟶ A) (f : M ⟶ N)
    (a : M ⟶ bimoduleRestrict q M) (b : N ⟶ bimoduleRestrict q N)
    (h : f.hom ≫ b.hom = a.hom ≫ f.hom) (hb : b.hom = 𝟙 N.X) :
    mapHom q f f a b h = 𝟙 (obj f).X := by
  apply mapHom_eq
  simp only [Category.id_comp, hb, Category.comp_id]

variable {A'' : Mon (Complex R)} {M'' N'' : Bimod A'' A''}
  (q' : A' ⟶ A'') (f'' : M'' ⟶ N'')
  (a' : M' ⟶ bimoduleRestrict q' M'') (b' : N' ⟶ bimoduleRestrict q' N'')
  (h' : f'.hom ≫ b'.hom = a'.hom ≫ f''.hom)
  (q'' : A ⟶ A'') (a'' : M ⟶ bimoduleRestrict q'' M'')
  (b'' : N ⟶ bimoduleRestrict q'' N'') (h'' : f.hom ≫ b''.hom = a''.hom ≫ f''.hom)

lemma mapHom_comp (hb : b''.hom = b.hom ≫ b'.hom) :
    mapHom q'' f f'' a'' b'' h'' = mapHom q f f' a b h ≫ mapHom q' f' f'' a' b' h' := by
  apply mapHom_eq
  rw [Category.assoc, mapHom_inclusion, ← Category.assoc, mapHom_inclusion, Category.assoc, hb]

end SerrePositivity.KST.LocalizingInvariants.DGBimoduleImage
