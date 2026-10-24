module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreClassAffine

/-!
概要：native class 遷移経路を零底へ戻し、fⱼ で後合成した実経路を計算する。
方針：底変更経路の元の射影と、同じ零層逆の厳密な右三角形を使う。
規約：ホモロジーの式でなく Path への元の代数射の一致。使われ方：Γ の右三角形。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Preadditive
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

lemma postnikovCommonClassTransitionIso_inv_zero :
    (postnikovCommonClassTransitionIso R hn f c d hj).inv ≫
      postnikovCommonClassTransitionToZero R hn f c d hj =
    SquareZero.baseChangeMap (postnikovCommonClassRetractBase R hn f c d (hj := hj) ≫
      postnikovTransition R (A.obj j).obj n 0 (by omega))
      (DGBimoduleShift.obj (postnikovLayerZeroBimodule R (A.obj j).obj n) 1) := by
  apply (cancel_epi (postnikovCommonClassTransitionIso R hn f c d hj).hom).1
  rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  exact (postnikovClassBaseZeroIso_map R (A.obj j).obj (postnikovCommonClassBase R hn f c d)
    n hn 1 (postnikovCommonClassRetractBase R hn f c d (hj := hj))).symm

lemma postnikovCommonClassTransitionWitness_zero :
    (postnikovCommonClassTransitionWitness R hn f c d e).hom ≫
      Path.map R (postnikovCommonClassTransitionToZero R hn f c d hj) =
        (postnikovCommonClassRetractWitness R hn f c d e).hom := by
  change ((postnikovCommonClassRetractRelativeWitness R hn f c d e).hom ≫
    Path.map R (postnikovCommonClassTransitionIso R hn f c d hj).inv) ≫ _ = _
  rw [Category.assoc, ← Path.map_comp, postnikovCommonClassTransitionIso_inv_zero,
    postnikovCommonClassRetractRelativeWitness, SquareZero.baseChangeWitness_map]

lemma postnikovCommonRightRetract_right : postnikovCommonRightRetract R hn f c d e ≫
    postnikovZeroClassMap R n 1 (f.app j).hom = postnikovCommonRightClassToZero R hn f c d ≫
      postnikovZeroClassMap R n 1 (B.transition hj).hom := by
  rw [postnikovCommonRightRetract, Category.assoc, e.shiftedClassMap_right]

lemma postnikovCommonClassTransitionWitness_zero_right :
    (postnikovCommonClassTransitionWitness R hn f c d e).hom ≫ Path.map R
      (postnikovCommonClassTransitionToZero R hn f c d hj ≫
        postnikovZeroClassMap R n 1 (f.app j).hom) =
    (postnikovCommonRightClassGlueWitness R hn f c d).hom ≫ Path.map R
      (postnikovCommonRightClassToZero R hn f c d ≫
        postnikovZeroClassMap R n 1 (B.transition hj).hom) := by
  rw [Path.map_comp, ← Category.assoc, postnikovCommonClassTransitionWitness_zero]
  change ((postnikovCommonRightClassGlueWitness R hn f c d).hom ≫
    Path.map R (postnikovCommonRightRetract R hn f c d e)) ≫ _ = _
  rw [Category.assoc, ← Path.map_comp, postnikovCommonRightRetract_right]

lemma postnikovCommonClassAffineRelative_zero_right_hom :
    ((postnikovCommonClassAffineRelative R hn f c d e).hom ≫ Path.map R
      (postnikovCommonClassTransitionToZero R hn f c d hj ≫
        postnikovZeroClassMap R n 1 (f.app j).hom)).hom =
    (postnikovCommonClassTransitionSource R hn f c d (hj := hj) ≫
      (postnikovCommonClassTransitionToZero R hn f c d hj ≫
        postnikovZeroClassMap R n 1 (f.app j).hom) ≫
      Path.diagonal R (postnikovZeroClassTarget R (B.obj j).obj n 1)).hom -
    ((postnikovCommonRightClassGlueWitness R hn f c d).hom ≫ Path.map R
      (postnikovCommonRightClassToZero R hn f c d ≫
        postnikovZeroClassMap R n 1 (B.transition hj).hom)).hom +
    ((postnikovCommonClassStandardWitness R hn f c d hj).hom ≫ Path.map R
      (postnikovCommonClassTransitionToZero R hn f c d hj ≫
        postnikovZeroClassMap R n 1 (f.app j).hom)).hom := by
  let z : SquareZero.algebra (postnikovCommonClassBase R hn f c d)
      (postnikovCommonClassTransitionLayer R hn f c d hj) ⟶
      postnikovZeroClassTarget R (B.obj j).obj n 1 :=
    postnikovCommonClassTransitionToZero R hn f c d hj ≫
      postnikovZeroClassMap R n 1 (f.app j).hom
  have h := congrArg (fun t => t ≫ (Path.map R z).hom)
    (postnikovCommonClassAffineRelative_hom_linear R hn f c d e)
  simpa only [z, add_comp, sub_comp, ← Mon.comp_hom', Category.assoc,
    Path.diagonal_naturality, postnikovCommonClassTransitionWitness_zero_right] using h

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovCommonCore
