module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreClassTransition

/-!
概要：遷移後の class の底変更経路を、元の層を制限した class 標的へ戻す。
方針：二つの底変更射影で両端を同定し、恒等係数同型の逆で経路を移す。
規約：元の二 class・A の係数遷移・P 上の定数射影を保持。使われ方：標準 class との比較。
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
  (d : PostnikovCommonLayerInverse R hn f c) {j : ℕ} {hj : j ≤ i}
  (e : PostnikovZeroLayerInverse R n f j i hj)

attribute [local instance] PostnikovRoofZeroSpan.refined_source_nonpositive
  PostnikovRoofZeroSpan.refined_target_nonpositive

def postnikovCommonClassTransitionTarget : postnikovCommonRightZeroGlueSource R hn f c d ⟶
    SquareZero.algebra (postnikovCommonClassBase R hn f c d)
      (postnikovCommonClassTransitionLayer R hn f c d hj) :=
 postnikovCommonRightGlueToCell R hn f c d ≫
  postnikovCommonClassTarget R hn f c d ≫ postnikovCommonClassTransitionMap R hn f c d hj

def postnikovCommonClassTransitionSource : postnikovCommonRightZeroGlueSource R hn f c d ⟶
    SquareZero.algebra (postnikovCommonClassBase R hn f c d)
      (postnikovCommonClassTransitionLayer R hn f c d hj) :=
 postnikovCommonRightGlueToCell R hn f c d ≫
  postnikovCommonClassSource R hn f c d ≫ postnikovCommonClassTransitionMap R hn f c d hj

lemma postnikovCommonClassTransitionTarget_projection :
    postnikovCommonClassTransitionTarget R hn f c d (hj := hj) ≫ SquareZero.projection _ _ =
      postnikovCommonRightZeroGlueProjection R hn f c d := by
  rw [postnikovCommonClassTransitionTarget, Category.assoc, Category.assoc,
    postnikovCommonClassTransitionMap, SquareZero.coefficientMap_projection,
    postnikovCommonClassTarget_projection, postnikovCommonRightGlueToCell_projection]

lemma postnikovCommonClassTransitionSource_projection :
    postnikovCommonClassTransitionSource R hn f c d (hj := hj) ≫ SquareZero.projection _ _ =
      postnikovCommonRightZeroGlueProjection R hn f c d := by
  rw [postnikovCommonClassTransitionSource, Category.assoc, Category.assoc,
    postnikovCommonClassTransitionMap, SquareZero.coefficientMap_projection,
    postnikovCommonClassSource_projection, postnikovCommonRightGlueToCell_projection]

lemma postnikovCommonClassTransitionTarget_zero :
    postnikovCommonClassTransitionTarget R hn f c d (hj := hj) ≫
      postnikovCommonClassTransitionToZero R hn f c d hj =
        postnikovCommonClassRetractTarget R hn f c d (hj := hj) := by
  rw [postnikovCommonClassTransitionTarget, Category.assoc, Category.assoc,
    postnikovCommonClassTransition_zero]
  rfl

lemma postnikovCommonClassTransitionSource_zero :
    postnikovCommonClassTransitionSource R hn f c d (hj := hj) ≫
      postnikovCommonClassTransitionToZero R hn f c d hj =
        postnikovCommonClassRetractSource R hn f c d (hj := hj) := by
  rw [postnikovCommonClassTransitionSource, Category.assoc, Category.assoc,
    postnikovCommonClassTransition_zero]
  rfl

lemma postnikovCommonClassRetractLeft_eq : postnikovCommonClassRetractLeft R hn f c d e =
    postnikovCommonClassTransitionTarget R hn f c d (hj := hj) ≫
      (postnikovCommonClassTransitionIso R hn f c d hj).hom := by
  apply SquareZero.baseChange_hom_ext
    (postnikovCommonClassRetractBase R hn f c d (hj := hj) ≫
      postnikovTransition R (A.obj j).obj n 0 (by omega))
    (DGBimoduleShift.obj (postnikovLayerZeroBimodule R (A.obj j).obj n) 1)
  · rw [postnikovCommonClassRetractLeft, SquareZero.baseChangeLift_projection,
      Category.assoc, postnikovCommonClassTransitionIso, postnikovClassBaseZeroIso_projection,
      postnikovCommonClassTransitionTarget_projection]
  · rw [postnikovCommonClassRetractLeft, SquareZero.baseChangeLift_map,
      Category.assoc, postnikovCommonClassTransitionIso, postnikovClassBaseZeroIso_map]
    exact (postnikovCommonClassTransitionTarget_zero R hn f c d (hj := hj)).symm

lemma postnikovCommonClassRetractRight_eq : postnikovCommonClassRetractRight R hn f c d e =
    postnikovCommonClassTransitionSource R hn f c d (hj := hj) ≫
      (postnikovCommonClassTransitionIso R hn f c d hj).hom := by
  apply SquareZero.baseChange_hom_ext
    (postnikovCommonClassRetractBase R hn f c d (hj := hj) ≫
      postnikovTransition R (A.obj j).obj n 0 (by omega))
    (DGBimoduleShift.obj (postnikovLayerZeroBimodule R (A.obj j).obj n) 1)
  · rw [postnikovCommonClassRetractRight, SquareZero.baseChangeLift_projection,
      Category.assoc, postnikovCommonClassTransitionIso, postnikovClassBaseZeroIso_projection,
      postnikovCommonClassTransitionSource_projection]
  · rw [postnikovCommonClassRetractRight, SquareZero.baseChangeLift_map,
      Category.assoc, postnikovCommonClassTransitionIso, postnikovClassBaseZeroIso_map]
    exact (postnikovCommonClassTransitionSource_zero R hn f c d (hj := hj)).symm

/-- 遷移後の元の二 class の像を、P に相対的な実乗法的経路で結ぶ。 -/
def postnikovCommonClassTransitionWitness : Path.Witness R
    (postnikovCommonClassTransitionTarget R hn f c d (hj := hj))
    (postnikovCommonClassTransitionSource R hn f c d (hj := hj)) where
  hom := (postnikovCommonClassRetractRelativeWitness R hn f c d e).hom ≫
    Path.map R (postnikovCommonClassTransitionIso R hn f c d hj).inv
  source_eq := by
    rw [Category.assoc, Path.map_source, ← Category.assoc,
      (postnikovCommonClassRetractRelativeWitness R hn f c d e).source_eq,
      postnikovCommonClassRetractLeft_eq, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  target_eq := by
    rw [Category.assoc, Path.map_target, ← Category.assoc,
      (postnikovCommonClassRetractRelativeWitness R hn f c d e).target_eq,
      postnikovCommonClassRetractRight_eq, Category.assoc, Iso.hom_inv_id, Category.comp_id]

lemma postnikovCommonClassTransitionWitness_projection :
    (postnikovCommonClassTransitionWitness R hn f c d e).hom ≫ Path.map R (SquareZero.projection _ _) =
      postnikovCommonRightZeroGlueProjection R hn f c d ≫
        Path.diagonal R (postnikovCommonClassBase R hn f c d) := by
  change (_ ≫ Path.map R (postnikovCommonClassTransitionIso R hn f c d hj).inv) ≫ _ = _
  rw [Category.assoc, ← Path.map_comp, postnikovCommonClassTransitionIso,
    postnikovClassBaseZeroIso_inv_projection, postnikovCommonClassRetractRelativeWitness_projection]

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovCommonCore
