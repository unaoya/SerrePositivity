module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovSourceImageClassSquare
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovPerturbedMapLaws

/-!
概要：正方形に沿う像係数の実平方零代数射は、恒等・合成を厳密に保つ。
方針：元の底の射と実係数像射の関手則を、直和射の二成分へ渡す。
規約：元の平方零代数を保持。使われ方：源側像拡大の関手則。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R] {B C B' C' B'' C'' : Mon (Complex R)}
  [B.X.IsStrictlyLE 0] [C.X.IsStrictlyLE 0] [B'.X.IsStrictlyLE 0] [C'.X.IsStrictlyLE 0]
  [B''.X.IsStrictlyLE 0] [C''.X.IsStrictlyLE 0] (n : ℤ) (hn : 0 ≤ n)

lemma postnikovSourceImageSquareZeroMap_id (f : B ⟶ C) :
    postnikovSourceImageSquareZeroMap R n hn f f (𝟙 B) (𝟙 C) (by simp) = 𝟙 _ := by
  let v : (postnikovShiftedLayerImage R f n hn 1).X ⟶
      (postnikovShiftedLayerImage R f n hn 1).X :=
    (postnikovShiftedLayerImageSquareMap R n hn 1 f f (𝟙 B) (𝟙 C) (by simp)).hom
  have hv : v = 𝟙 _ := postnikovShiftedLayerImageSquareMap_id_hom R n hn 1 f
  have hb : (postnikovMap R (𝟙 B) n).hom = 𝟙 _ := (postnikovComplex R n).map_id B
  apply Mon.Hom.ext
  change biprod.map (postnikovMap R (𝟙 B) n).hom v = 𝟙 _
  rw [hb, hv]
  exact cochainBiprodMap_id

lemma postnikovSourceImageSquareZeroMap_comp
    (f : B ⟶ C) (f' : B' ⟶ C') (f'' : B'' ⟶ C'')
    (s : B ⟶ B') (t : C ⟶ C') (s' : B' ⟶ B'') (t' : C' ⟶ C'')
    (h : f ≫ t = s ≫ f') (h' : f' ≫ t' = s' ≫ f'') :
    postnikovSourceImageSquareZeroMap R n hn f f'' (s ≫ s') (t ≫ t')
      (by rw [← Category.assoc, h, Category.assoc, h', ← Category.assoc]) =
        postnikovSourceImageSquareZeroMap R n hn f f' s t h ≫
          postnikovSourceImageSquareZeroMap R n hn f' f'' s' t' h' := by
  apply Mon.Hom.ext
  change biprod.map (postnikovMap R (s ≫ s') n).hom
    ((postnikovShiftedLayerImageSquareMap R n hn 1 f f'' (s ≫ s') (t ≫ t') _).hom :
      (postnikovShiftedLayerImage R f n hn 1).X ⟶ (postnikovShiftedLayerImage R f'' n hn 1).X) =
        biprod.map (postnikovMap R s n).hom
          ((postnikovShiftedLayerImageSquareMap R n hn 1 f f' s t h).hom :
            (postnikovShiftedLayerImage R f n hn 1).X ⟶
              (postnikovShiftedLayerImage R f' n hn 1).X) ≫
        biprod.map (postnikovMap R s' n).hom
          ((postnikovShiftedLayerImageSquareMap R n hn 1 f' f'' s' t' h').hom :
            (postnikovShiftedLayerImage R f' n hn 1).X ⟶
              (postnikovShiftedLayerImage R f'' n hn 1).X)
  have hb : (postnikovMap R (s ≫ s') n).hom =
      (postnikovMap R s n).hom ≫ (postnikovMap R s' n).hom :=
    (postnikovComplex R n).map_comp s s'
  rw [cochainBiprodMap_comp, hb, postnikovShiftedLayerImageSquareMap_comp_hom]

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
