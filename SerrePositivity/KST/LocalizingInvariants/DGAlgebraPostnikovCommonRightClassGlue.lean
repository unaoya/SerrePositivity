module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonRightZeroGlue
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonRightZeroBaseIso

/-!
概要：共通零標的で貼り合わせた経路を、元の共通底上の右 class 標的へ戻す。
方針：底変更の普遍性で両端を同定し、元の係数同型の逆で実経路を後合成する。
規約：元の二 class の右像と底への定数射影を保持。使われ方：次段の kernel 障害消去。
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

def postnikovCommonRightGlueToCell : postnikovCommonRightZeroGlueSource R f c d ⟶
    cellResolution R (postnikovCommonClassBase R f c d) :=
  cellPathNonpositiveProjection R (postnikovCommonRightCellSource R f c d) ≫
    cellPathNonpositiveToCell R (postnikovCommonClassBase R f c d)

lemma postnikovCommonRightGlueToCell_projection : postnikovCommonRightGlueToCell R f c d ≫
    cellAugmentation R (postnikovCommonClassBase R f c d) =
      postnikovCommonRightZeroGlueProjection R f c d := by
  rw [postnikovCommonRightGlueToCell, Category.assoc, cellPathNonpositiveToCell_projection]
  rfl

def postnikovCommonRightGlueTarget := postnikovCommonRightGlueToCell R f c d ≫
  (postnikovCommonClassTarget R f c d ≫ postnikovCommonRightClassNumeratorMap R f c d)

def postnikovCommonRightGlueSource := postnikovCommonRightGlueToCell R f c d ≫
  (postnikovCommonClassSource R f c d ≫ postnikovCommonRightClassNumeratorMap R f c d)

lemma postnikovCommonRightGlueTarget_projection : postnikovCommonRightGlueTarget R f c d ≫
    SquareZero.projection _ _ = postnikovCommonRightZeroGlueProjection R f c d := by
  rw [postnikovCommonRightGlueTarget, Category.assoc, Category.assoc,
    postnikovCommonRightClassNumeratorMap_projection, postnikovCommonClassTarget_projection,
    postnikovCommonRightGlueToCell_projection]

lemma postnikovCommonRightGlueSource_projection : postnikovCommonRightGlueSource R f c d ≫
    SquareZero.projection _ _ = postnikovCommonRightZeroGlueProjection R f c d := by
  rw [postnikovCommonRightGlueSource, Category.assoc, Category.assoc,
    postnikovCommonRightClassNumeratorMap_projection, postnikovCommonClassSource_projection,
    postnikovCommonRightGlueToCell_projection]

lemma postnikovCommonRightZeroGlueLeft_eq : postnikovCommonRightZeroGlueLeft R f c d =
    postnikovCommonRightGlueTarget R f c d ≫ (postnikovCommonRightZeroBaseIso R f c d).hom := by
  apply SquareZero.baseChange_hom_ext (postnikovCommonRightZeroBase R f c d)
    (DGBimoduleShift.obj (postnikovLayerZeroBimodule R (B.obj i).obj 1) 1)
  · rw [postnikovCommonRightZeroGlueLeft, SquareZero.baseChangeLift_projection,
      Category.assoc, postnikovCommonRightZeroBaseIso_projection,
      postnikovCommonRightGlueTarget_projection]
  · rw [postnikovCommonRightZeroGlueLeft, SquareZero.baseChangeLift_map,
      Category.assoc, postnikovCommonRightZeroBaseIso_map]
    simp only [postnikovCommonRightGlueTarget, postnikovCommonRightGlueToCell,
      postnikovCommonRightZeroImageTarget, Category.assoc]

lemma postnikovCommonRightZeroGlueRight_eq : postnikovCommonRightZeroGlueRight R f c d =
    postnikovCommonRightGlueSource R f c d ≫ (postnikovCommonRightZeroBaseIso R f c d).hom := by
  apply SquareZero.baseChange_hom_ext (postnikovCommonRightZeroBase R f c d)
    (DGBimoduleShift.obj (postnikovLayerZeroBimodule R (B.obj i).obj 1) 1)
  · rw [postnikovCommonRightZeroGlueRight, SquareZero.baseChangeLift_projection,
      Category.assoc, postnikovCommonRightZeroBaseIso_projection,
      postnikovCommonRightGlueSource_projection]
  · rw [postnikovCommonRightZeroGlueRight, SquareZero.baseChangeLift_map,
      Category.assoc, postnikovCommonRightZeroBaseIso_map]
    simp only [postnikovCommonRightGlueSource, postnikovCommonRightGlueToCell,
      postnikovCommonRightZeroImageSource, Category.assoc]

/-- 元の二 class の右像を、同じ非正次数源と元の底に相対的な実経路で結ぶ。 -/
def postnikovCommonRightClassGlueWitness : Path.Witness R
    (postnikovCommonRightGlueTarget R f c d) (postnikovCommonRightGlueSource R f c d) where
  hom := (postnikovCommonRightZeroGlueRelativeWitness R f c d).hom ≫
    Path.map R (postnikovCommonRightZeroBaseIso R f c d).inv
  source_eq := by
    rw [Category.assoc, Path.map_source, ← Category.assoc,
      (postnikovCommonRightZeroGlueRelativeWitness R f c d).source_eq,
      postnikovCommonRightZeroGlueLeft_eq, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  target_eq := by
    rw [Category.assoc, Path.map_target, ← Category.assoc,
      (postnikovCommonRightZeroGlueRelativeWitness R f c d).target_eq,
      postnikovCommonRightZeroGlueRight_eq, Category.assoc, Iso.hom_inv_id, Category.comp_id]

lemma postnikovCommonRightClassGlueWitness_projection :
    (postnikovCommonRightClassGlueWitness R f c d).hom ≫ Path.map R (SquareZero.projection _ _) =
      postnikovCommonRightZeroGlueProjection R f c d ≫
        Path.diagonal R (postnikovCommonClassBase R f c d) := by
  change (_ ≫ Path.map R (postnikovCommonRightZeroBaseIso R f c d).inv) ≫ _ = _
  rw [Category.assoc, ← Path.map_comp, postnikovCommonRightZeroBaseIso_inv_projection,
    postnikovCommonRightZeroGlueRelativeWitness_projection]

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
