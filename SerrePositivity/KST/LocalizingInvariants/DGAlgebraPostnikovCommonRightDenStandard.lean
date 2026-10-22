module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonRightDenBaseIso
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonRightClass
public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroCoefficientFunctor

/-!
概要：共通底の右 class 標的を標準の制限層の平方零代数と実同型で比較する。
方針：恒等 underlying 層同型を shift し、元の B の class を元の分母側の指定底で引き戻す。
規約：元の class を結ぶ経路は未主張。使われ方：class の像の比較の基準射。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
open ProExcision
variable (R : Type u) [CommRing R] {A B : Tower (NonpositiveAlgebra R)} (f : LevelHom A B)
  {i m : ℕ} {hi : i ≤ m} (c : NonpositiveInverseRoof R (f.map (postnikovFunctor R 1)) i m hi)
  (d : PostnikovCommonLayerInverse R f c)

def postnikovCommonRightShiftedDenBaseIso (s : ℤ) :
    bimoduleRestrict (postnikovCommonRightDenBase R f c d)
      (postnikovShiftedLayerBimodule R (B.obj i).obj 1 (by omega) s) ≅
        DGBimoduleShift.obj (postnikovCommonRightLayer R f c d) s :=
  (DGBimoduleShift.restrictionIso (postnikovCommonRightDenBase R f c d)
    (postnikovLayerBaseBimodule R (B.obj i).obj 1 (by omega)) s).symm ≪≫
      (DGBimoduleShift.functor _ s).mapIso (postnikovCommonRightDenBaseIso R f c d)

lemma postnikovCommonRightShiftedDenBaseIso_hom (s : ℤ) :
    (postnikovCommonRightShiftedDenBaseIso R f c d s).hom.hom =
      𝟙 ((postnikovLayer R (B.obj i).obj 1)⟦s⟧) := by
  change 𝟙 _ ≫ (postnikovCommonRightDenBaseIso R f c d).hom.hom⟦s⟧' = _
  rw [postnikovCommonRightDenBaseIso_hom]
  change 𝟙 ((postnikovLayer R (B.obj i).obj 1)⟦s⟧) ≫
    (shiftFunctor (Complex R) s).map (𝟙 (postnikovLayer R (B.obj i).obj 1)) = 𝟙 _
  rw [(shiftFunctor (Complex R) s).map_id]
  exact Category.id_comp _

def postnikovCommonRightDenClassIso :
    SquareZero.algebra (postnikovCommonClassBase R f c d)
      (bimoduleRestrict (postnikovCommonRightDenBase R f c d)
        (postnikovShiftedLayerBimodule R (B.obj i).obj 1 (by omega) 1)) ≅
          postnikovCommonRightClassTarget R f c d :=
  SquareZero.coefficientIso _ (postnikovCommonRightShiftedDenBaseIso R f c d 1)

lemma postnikovCommonRightDenClassIso_projection : (postnikovCommonRightDenClassIso R f c d).hom ≫
    SquareZero.projection _ _ = SquareZero.projection _ _ :=
  SquareZero.coefficientMap_projection _ _

def postnikovCommonRightDenStandardClass : cellResolution R (postnikovCommonClassBase R f c d) ⟶
    postnikovCommonRightClassTarget R f c d :=
  postnikovCellClassOver R (B.obj i).obj (postnikovCommonClassBase R f c d) 1 (by omega)
    (postnikovCommonRightDenBase R f c d) ≫ (postnikovCommonRightDenClassIso R f c d).hom

lemma postnikovCommonRightDenStandardClass_projection :
    postnikovCommonRightDenStandardClass R f c d ≫
    SquareZero.projection _ _ = cellAugmentation R (postnikovCommonClassBase R f c d) := by
  rw [postnikovCommonRightDenStandardClass, Category.assoc,
    postnikovCommonRightDenClassIso_projection]
  exact postnikovCellClassOver_projection _ _ _ _ _ _

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
