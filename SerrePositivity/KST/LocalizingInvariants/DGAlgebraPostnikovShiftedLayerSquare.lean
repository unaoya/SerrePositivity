module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovShiftedLayer
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovExtensionConeMap
public import SerrePositivity.KST.LocalizingInvariants.BimoduleRestrictionSquareMap

/-!
概要：元の代数の可換正方形を、底変更を含む shift 層の実双加群正方形へ送る。
方針：元の切断と層の関手則、制限双加群の実正方形射を使う。
規約：任意整数 shift と元の四辺を保持。使われ方：Postnikov 係数像の正方形作用。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R] {B C D : Mon (Complex R)}
  [B.X.IsStrictlyLE 0] [C.X.IsStrictlyLE 0] [D.X.IsStrictlyLE 0]
  (n : ℤ) (hn : 0 ≤ n) (k : ℤ)

lemma postnikovMap_identity : postnikovMap R (𝟙 B) n = 𝟙 (postnikov R B n) := by
  apply Mon.Hom.ext
  exact (postnikovComplex R n).map_id B

lemma postnikovMap_composition (f : B ⟶ C) (g : C ⟶ D) :
    postnikovMap R (f ≫ g) n = postnikovMap R f n ≫ postnikovMap R g n := by
  apply Mon.Hom.ext
  exact (postnikovComplex R n).map_comp f g

lemma postnikovShiftedLayerMap_id_hom :
    (postnikovShiftedLayerMap R B n hn k (𝟙 B)).hom = 𝟙 _ := by
  rw [postnikovShiftedLayerMap_hom, postnikovLayerMap_id]
  exact (CategoryTheory.shiftFunctor (Complex R) k).map_id _

lemma postnikovShiftedLayerMap_comp_hom (f : B ⟶ C) (g : C ⟶ D) :
    (postnikovShiftedLayerMap R B n hn k (f ≫ g)).hom =
      (postnikovShiftedLayerMap R B n hn k f).hom ≫
        (postnikovShiftedLayerMap R C n hn k g).hom := by
  rw [postnikovShiftedLayerMap_hom, postnikovShiftedLayerMap_hom, postnikovShiftedLayerMap_hom,
    postnikovLayerMap_comp]
  exact (CategoryTheory.shiftFunctor (Complex R) k).map_comp _ _

variable {B' C' : Mon (Complex R)} [B'.X.IsStrictlyLE 0] [C'.X.IsStrictlyLE 0]
  (f : B ⟶ C) (f' : B' ⟶ C') (s : B ⟶ B') (t : C ⟶ C') (h : f ≫ t = s ≫ f')

include h in
lemma postnikovMap_square : postnikovMap R f n ≫ postnikovMap R t n =
    postnikovMap R s n ≫ postnikovMap R f' n := by
  apply Mon.Hom.ext
  change (postnikovComplex R n).map f ≫ (postnikovComplex R n).map t =
    (postnikovComplex R n).map s ≫ (postnikovComplex R n).map f'
  rw [← CategoryTheory.Functor.map_comp, h, CategoryTheory.Functor.map_comp]

include h in
lemma postnikovShiftedLayerMap_square : (postnikovShiftedLayerMap R B n hn k f).hom ≫
    (postnikovShiftedLayerMap R C n hn k t).hom =
      (postnikovShiftedLayerMap R B n hn k s).hom ≫
        (postnikovShiftedLayerMap R B' n hn k f').hom := by
  rw [← postnikovShiftedLayerMap_comp_hom, h, postnikovShiftedLayerMap_comp_hom]

def postnikovShiftedLayerSquareTargetMap :
    bimoduleRestrict (postnikovMap R f n) (postnikovShiftedLayerBimodule R C n hn k) ⟶
      bimoduleRestrict (postnikovMap R s n)
        (bimoduleRestrict (postnikovMap R f' n) (postnikovShiftedLayerBimodule R C' n hn k)) :=
  bimoduleRestrictSquareMap (postnikovMap R f n) (postnikovMap R f' n)
    (postnikovMap R s n) (postnikovMap R t n) (postnikovMap_square R n f f' s t h)
    (postnikovShiftedLayerMap R C n hn k t)

lemma postnikovShiftedLayerSquareTargetMap_hom :
    (postnikovShiftedLayerSquareTargetMap R n hn k f f' s t h).hom =
      (postnikovShiftedLayerMap R C n hn k t).hom := rfl

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
