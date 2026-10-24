module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreRightBaseIso
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreRightClass
public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroCoefficientFunctor

/-!
概要：共通底の右 class 標的を標準の制限層の平方零代数と実同型で比較する。
方針：恒等 underlying 層同型を shift し、元の B の class を指定底で引き戻す。
規約：元の class を結ぶ経路は未主張。使われ方：class の像の比較の基準射。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovCommonCore
open ProExcision
variable (R : Type u) [CommRing R] {n : ℤ} (hn : 0 ≤ n)
  {A B : Tower (NonpositiveAlgebra R)} (f : LevelHom A B)
  {i m : ℕ} {hi : i ≤ m} (c : NonpositiveInverseRoof R (f.map (lowerFunctor R n hn)) i m hi)
  (d : PostnikovCommonLayerInverse R hn f c)

attribute [local instance] PostnikovRoofZeroSpan.refined_source_nonpositive
  PostnikovRoofZeroSpan.refined_target_nonpositive

def postnikovCommonRightShiftedBaseIso (s : ℤ) :
    bimoduleRestrict (postnikovCommonRightBase R hn f c d)
      (postnikovShiftedLayerBimodule R (B.obj i).obj n hn s) ≅
        DGBimoduleShift.obj (postnikovCommonRightLayer R hn f c d) s :=
  (DGBimoduleShift.restrictionIso (postnikovCommonRightBase R hn f c d)
    (postnikovLayerBaseBimodule R (B.obj i).obj n hn) s).symm ≪≫
      (DGBimoduleShift.functor _ s).mapIso (postnikovCommonRightBaseIso R hn f c d)

lemma postnikovCommonRightShiftedBaseIso_hom (s : ℤ) :
    (postnikovCommonRightShiftedBaseIso R hn f c d s).hom.hom =
      𝟙 ((postnikovLayer R (B.obj i).obj n)⟦s⟧) := by
  change 𝟙 _ ≫ (postnikovCommonRightBaseIso R hn f c d).hom.hom⟦s⟧' = _
  rw [postnikovCommonRightBaseIso_hom]
  change 𝟙 ((postnikovLayer R (B.obj i).obj n)⟦s⟧) ≫
    (shiftFunctor (Complex R) s).map (𝟙 (postnikovLayer R (B.obj i).obj n)) = 𝟙 _
  rw [(shiftFunctor (Complex R) s).map_id]
  exact Category.id_comp _

def postnikovCommonRightClassIso :
    SquareZero.algebra (postnikovCommonClassBase R hn f c d)
      (bimoduleRestrict (postnikovCommonRightBase R hn f c d)
        (postnikovShiftedLayerBimodule R (B.obj i).obj n hn 1)) ≅
          postnikovCommonRightClassTarget R hn f c d :=
  SquareZero.coefficientIso _ (postnikovCommonRightShiftedBaseIso R hn f c d 1)

lemma postnikovCommonRightClassIso_projection : (postnikovCommonRightClassIso R hn f c d).hom ≫
    SquareZero.projection _ _ = SquareZero.projection _ _ :=
  SquareZero.coefficientMap_projection _ _

def postnikovCommonRightStandardClass : cellResolution R (postnikovCommonClassBase R hn f c d) ⟶
    postnikovCommonRightClassTarget R hn f c d :=
  postnikovCellClassOver R (B.obj i).obj (postnikovCommonClassBase R hn f c d) n hn
    (postnikovCommonRightBase R hn f c d) ≫ (postnikovCommonRightClassIso R hn f c d).hom

lemma postnikovCommonRightStandardClass_projection : postnikovCommonRightStandardClass R hn f c d ≫
    SquareZero.projection _ _ = cellAugmentation R (postnikovCommonClassBase R hn f c d) := by
  rw [postnikovCommonRightStandardClass, Category.assoc, postnikovCommonRightClassIso_projection]
  exact postnikovCellClassOver_projection _ _ _ _ _ _

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovCommonCore
