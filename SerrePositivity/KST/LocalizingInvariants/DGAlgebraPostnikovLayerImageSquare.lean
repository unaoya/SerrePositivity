module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovShiftedLayerSquare
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovLayerImage
public import SerrePositivity.KST.LocalizingInvariants.DGBimoduleImageMapLaws

/-!
概要：元の代数の可換正方形を、実係数像の底変更を含む双加群射へ送る。
方針：元の shift 層正方形に、実係数像の射を適用する。
規約：元の像包含・像射影との式を保持。使われ方：源 class の像拡大の遷移。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R] {B C B' C' : Mon (Complex R)}
  [B.X.IsStrictlyLE 0] [C.X.IsStrictlyLE 0] [B'.X.IsStrictlyLE 0] [C'.X.IsStrictlyLE 0]
  (n : ℤ) (hn : 0 ≤ n) (k : ℤ)
  (f : B ⟶ C) (f' : B' ⟶ C') (s : B ⟶ B') (t : C ⟶ C') (h : f ≫ t = s ≫ f')

def postnikovShiftedLayerImageSquareMap : postnikovShiftedLayerImage R f n hn k ⟶
    bimoduleRestrict (postnikovMap R s n) (postnikovShiftedLayerImage R f' n hn k) :=
  DGBimoduleImage.map (postnikovMap R s n) (postnikovShiftedLayerMap R B n hn k f)
    (postnikovShiftedLayerMap R B' n hn k f') (postnikovShiftedLayerMap R B n hn k s)
    (postnikovShiftedLayerSquareTargetMap R n hn k f f' s t h)
    (postnikovShiftedLayerMap_square R n hn k f f' s t h)

lemma postnikovShiftedLayerImageSquareMap_inclusion :
    (postnikovShiftedLayerImageSquareMap R n hn k f f' s t h).hom ≫
      (postnikovShiftedLayerImageInclusion R f' n hn k).hom =
        (postnikovShiftedLayerImageInclusion R f n hn k).hom ≫
          (postnikovShiftedLayerMap R C n hn k t).hom :=
  DGBimoduleImage.mapHom_inclusion _ _ _ _ _ _

lemma postnikovShiftedLayerImageSquareMap_projection :
    (postnikovShiftedLayerImageProjection R f n hn k).hom ≫
      (postnikovShiftedLayerImageSquareMap R n hn k f f' s t h).hom =
        (postnikovShiftedLayerMap R B n hn k s).hom ≫
          (postnikovShiftedLayerImageProjection R f' n hn k).hom :=
  DGBimoduleImage.mapHom_projection _ _ _ _ _ _

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
