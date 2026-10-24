module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreRightZeroGlue
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreRightZeroBaseIso

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
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovCommonCore
open ProExcision
variable (R : Type u) [CommRing R] {n : ℤ} (hn : 0 ≤ n)
  {A B : Tower (NonpositiveAlgebra R)} (f : LevelHom A B)
  {i m : ℕ} {hi : i ≤ m} (c : NonpositiveInverseRoof R (f.map (lowerFunctor R n hn)) i m hi)
  (d : PostnikovCommonLayerInverse R hn f c)

attribute [local instance] PostnikovRoofZeroSpan.refined_source_nonpositive
  PostnikovRoofZeroSpan.refined_target_nonpositive

def postnikovCommonRightGlueToCell : postnikovCommonRightZeroGlueSource R hn f c d ⟶
    cellResolution R (postnikovCommonClassBase R hn f c d) :=
  cellPathNonpositiveProjection R (postnikovCommonRightCellSource R hn f c d) ≫
    cellPathNonpositiveToCell R (postnikovCommonClassBase R hn f c d)

lemma postnikovCommonRightGlueToCell_projection : postnikovCommonRightGlueToCell R hn f c d ≫
    cellAugmentation R (postnikovCommonClassBase R hn f c d) =
      postnikovCommonRightZeroGlueProjection R hn f c d := by
  rw [postnikovCommonRightGlueToCell, Category.assoc, cellPathNonpositiveToCell_projection]
  rfl

def postnikovCommonRightGlueTarget := postnikovCommonRightGlueToCell R hn f c d ≫
  (postnikovCommonClassTarget R hn f c d ≫ postnikovCommonRightClassNumeratorMap R hn f c d)

def postnikovCommonRightGlueSource := postnikovCommonRightGlueToCell R hn f c d ≫
  (postnikovCommonClassSource R hn f c d ≫ postnikovCommonRightClassNumeratorMap R hn f c d)

lemma postnikovCommonRightGlueTarget_projection : postnikovCommonRightGlueTarget R hn f c d ≫
    SquareZero.projection _ _ = postnikovCommonRightZeroGlueProjection R hn f c d := by
  rw [postnikovCommonRightGlueTarget, Category.assoc, Category.assoc,
    postnikovCommonRightClassNumeratorMap_projection, postnikovCommonClassTarget_projection,
    postnikovCommonRightGlueToCell_projection]

lemma postnikovCommonRightGlueSource_projection : postnikovCommonRightGlueSource R hn f c d ≫
    SquareZero.projection _ _ = postnikovCommonRightZeroGlueProjection R hn f c d := by
  rw [postnikovCommonRightGlueSource, Category.assoc, Category.assoc,
    postnikovCommonRightClassNumeratorMap_projection, postnikovCommonClassSource_projection,
    postnikovCommonRightGlueToCell_projection]

lemma postnikovCommonRightZeroGlueLeft_eq : postnikovCommonRightZeroGlueLeft R hn f c d =
    postnikovCommonRightGlueTarget R hn f c d ≫ (postnikovCommonRightZeroBaseIso R hn f c d).hom := by
  apply SquareZero.baseChange_hom_ext (postnikovCommonRightZeroBase R hn f c d)
    (DGBimoduleShift.obj (postnikovLayerZeroBimodule R (B.obj i).obj n) 1)
  · rw [postnikovCommonRightZeroGlueLeft, SquareZero.baseChangeLift_projection,
      Category.assoc, postnikovCommonRightZeroBaseIso_projection,
      postnikovCommonRightGlueTarget_projection]
  · rw [postnikovCommonRightZeroGlueLeft, SquareZero.baseChangeLift_map,
      Category.assoc, postnikovCommonRightZeroBaseIso_map]
    simp only [postnikovCommonRightGlueTarget, postnikovCommonRightGlueToCell,
      postnikovCommonRightZeroImageTarget, Category.assoc]

lemma postnikovCommonRightZeroGlueRight_eq : postnikovCommonRightZeroGlueRight R hn f c d =
    postnikovCommonRightGlueSource R hn f c d ≫ (postnikovCommonRightZeroBaseIso R hn f c d).hom := by
  apply SquareZero.baseChange_hom_ext (postnikovCommonRightZeroBase R hn f c d)
    (DGBimoduleShift.obj (postnikovLayerZeroBimodule R (B.obj i).obj n) 1)
  · rw [postnikovCommonRightZeroGlueRight, SquareZero.baseChangeLift_projection,
      Category.assoc, postnikovCommonRightZeroBaseIso_projection,
      postnikovCommonRightGlueSource_projection]
  · rw [postnikovCommonRightZeroGlueRight, SquareZero.baseChangeLift_map,
      Category.assoc, postnikovCommonRightZeroBaseIso_map]
    simp only [postnikovCommonRightGlueSource, postnikovCommonRightGlueToCell,
      postnikovCommonRightZeroImageSource, Category.assoc]

/-- 元の二 class の右像を、同じ非正次数源と元の底に相対的な実経路で結ぶ。 -/
def postnikovCommonRightClassGlueWitness : Path.Witness R
    (postnikovCommonRightGlueTarget R hn f c d) (postnikovCommonRightGlueSource R hn f c d) where
  hom := (postnikovCommonRightZeroGlueRelativeWitness R hn f c d).hom ≫
    Path.map R (postnikovCommonRightZeroBaseIso R hn f c d).inv
  source_eq := by
    rw [Category.assoc, Path.map_source, ← Category.assoc,
      (postnikovCommonRightZeroGlueRelativeWitness R hn f c d).source_eq,
      postnikovCommonRightZeroGlueLeft_eq, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  target_eq := by
    rw [Category.assoc, Path.map_target, ← Category.assoc,
      (postnikovCommonRightZeroGlueRelativeWitness R hn f c d).target_eq,
      postnikovCommonRightZeroGlueRight_eq, Category.assoc, Iso.hom_inv_id, Category.comp_id]

lemma postnikovCommonRightClassGlueWitness_projection :
    (postnikovCommonRightClassGlueWitness R hn f c d).hom ≫ Path.map R (SquareZero.projection _ _) =
      postnikovCommonRightZeroGlueProjection R hn f c d ≫
        Path.diagonal R (postnikovCommonClassBase R hn f c d) := by
  change (_ ≫ Path.map R (postnikovCommonRightZeroBaseIso R hn f c d).inv) ≫ _ = _
  rw [Category.assoc, ← Path.map_comp, postnikovCommonRightZeroBaseIso_inv_projection,
    postnikovCommonRightZeroGlueRelativeWitness_projection]

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovCommonCore
