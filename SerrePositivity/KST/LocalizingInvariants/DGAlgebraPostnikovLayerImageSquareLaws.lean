module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovLayerImageSquare

/-!
概要：元の正方形から得る Postnikov 係数像の射は、恒等と合成を厳密に保つ。
方針：元の包含による一意性と、元の shift 層射の恒等・合成則を使う。
規約：underlying の実鎖写像の式。使われ方：像拡大の図式と遷移の構成。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R] {B C B' C' B'' C'' : Mon (Complex R)}
  [B.X.IsStrictlyLE 0] [C.X.IsStrictlyLE 0] [B'.X.IsStrictlyLE 0] [C'.X.IsStrictlyLE 0]
  [B''.X.IsStrictlyLE 0] [C''.X.IsStrictlyLE 0] (n : ℤ) (hn : 0 ≤ n) (k : ℤ)

lemma postnikovShiftedLayerImageSquareMap_id_hom (f : B ⟶ C) :
    (postnikovShiftedLayerImageSquareMap R n hn k f f (𝟙 B) (𝟙 C) (by simp)).hom = 𝟙 _ := by
  apply DGBimoduleImage.mapHom_identity
  exact postnikovShiftedLayerMap_id_hom R n hn k

lemma postnikovShiftedLayerImageSquareMap_comp_hom
    (f : B ⟶ C) (f' : B' ⟶ C') (f'' : B'' ⟶ C'')
    (s : B ⟶ B') (t : C ⟶ C') (s' : B' ⟶ B'') (t' : C' ⟶ C'')
    (h : f ≫ t = s ≫ f') (h' : f' ≫ t' = s' ≫ f'') :
    (postnikovShiftedLayerImageSquareMap R n hn k f f'' (s ≫ s') (t ≫ t')
      (by rw [← Category.assoc, h, Category.assoc, h', ← Category.assoc])).hom =
        (postnikovShiftedLayerImageSquareMap R n hn k f f' s t h).hom ≫
          (postnikovShiftedLayerImageSquareMap R n hn k f' f'' s' t' h').hom := by
  apply DGBimoduleImage.mapHom_comp
  exact postnikovShiftedLayerMap_comp_hom R n hn k t t'

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
