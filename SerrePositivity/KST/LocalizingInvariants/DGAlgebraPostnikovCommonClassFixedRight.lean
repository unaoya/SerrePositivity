module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonClassFixedTransition
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonClassAffineRight

/-!
概要：新しい class 互換性を fⱼ で移した経路を、元の B 遷移と指定右貼合せで計算する。
方針：同じ係数逆の厳密な右三角形と底変更射影を使う。
規約：全経路の実射の式を保つ。使われ方：組み直した Γ の右三角形。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Preadditive
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
open ProExcision
variable (R : Type u) [CommRing R] {A B : Tower (NonpositiveAlgebra R)} (f : LevelHom A B)
  {i m : ℕ} {hi : i ≤ m} (c : NonpositiveInverseRoof R (f.map (postnikovFunctor R 1)) i m hi)
  (d : PostnikovCommonLayerInverse R f c) {j : ℕ} {hj : j ≤ i}
  (e : PostnikovZeroLayerInverse R 1 f j i hj)

lemma postnikovCommonClassFixedTransition_zero :
    (postnikovCommonClassFixedTransitionWitness R f c d e).hom ≫
      Path.map R (postnikovCommonClassTransitionToZero R f c d hj) =
    (postnikovCommonClassFixedRetractWitness R f c d e).hom := by
  change ((postnikovCommonClassFixedRetractRelativeWitness R f c d e).hom ≫
    Path.map R (postnikovCommonClassTransitionIso R f c d hj).inv) ≫ _ = _
  rw [Category.assoc, ← Path.map_comp, postnikovCommonClassTransitionIso_inv_zero,
    postnikovCommonClassFixedRetractRelativeWitness, SquareZero.baseChangeWitness_map]

lemma postnikovCommonClassFixedTransition_zero_right :
    (postnikovCommonClassFixedTransitionWitness R f c d e).hom ≫ Path.map R
      (postnikovCommonClassTransitionToZero R f c d hj ≫
        postnikovZeroClassMap R 1 1 (f.app j).hom) =
    (postnikovCommonRightFixedClassGlueWitness R f c d).hom ≫ Path.map R
      (postnikovCommonRightClassToZero R f c d ≫
        postnikovZeroClassMap R 1 1 (B.transition hj).hom) := by
  rw [Path.map_comp, ← Category.assoc, postnikovCommonClassFixedTransition_zero]
  change ((postnikovCommonRightFixedClassGlueWitness R f c d).hom ≫
    Path.map R (postnikovCommonRightRetract R f c d e)) ≫ _ = _
  rw [Category.assoc, ← Path.map_comp, postnikovCommonRightRetract_right]

lemma postnikovCommonClassFixedCompatibility_linear :
    (postnikovCommonClassFixedCompatibility R f c d e).hom.hom =
    (postnikovCommonClassTransitionSource R f c d (hj := hj) ≫ Path.diagonal R _).hom -
      (postnikovCommonClassFixedTransitionWitness R f c d e).hom.hom +
      (postnikovCommonClassStandardWitness R f c d hj).hom.hom := by
  change (((postnikovCommonClassFixedTransitionRelative R f c d e).reverse).comp _).hom.hom = _
  rw [SquareZero.RelativeWitness.comp_hom_linear, SquareZero.RelativeWitness.reverse_hom_linear]
  change (postnikovCommonClassTransitionTarget R f c d (hj := hj) ≫ Path.diagonal R _).hom -
      (postnikovCommonClassFixedTransitionWitness R f c d e).hom.hom +
      (postnikovCommonClassTransitionSource R f c d (hj := hj) ≫ Path.diagonal R _).hom -
      (postnikovCommonClassTransitionTarget R f c d (hj := hj) ≫ Path.diagonal R _).hom +
      (postnikovCommonClassStandardWitness R f c d hj).hom.hom = _
  abel

lemma postnikovCommonClassFixedCompatibility_zero_right :
    ((postnikovCommonClassFixedCompatibility R f c d e).hom ≫ Path.map R
      (postnikovCommonClassTransitionToZero R f c d hj ≫
        postnikovZeroClassMap R 1 1 (f.app j).hom)).hom =
    (postnikovCommonClassTransitionSource R f c d (hj := hj) ≫
      (postnikovCommonClassTransitionToZero R f c d hj ≫
        postnikovZeroClassMap R 1 1 (f.app j).hom) ≫
      Path.diagonal R (postnikovZeroClassTarget R (B.obj j).obj 1 1)).hom -
    ((postnikovCommonRightFixedClassGlueWitness R f c d).hom ≫ Path.map R
      (postnikovCommonRightClassToZero R f c d ≫
        postnikovZeroClassMap R 1 1 (B.transition hj).hom)).hom +
    ((postnikovCommonClassStandardWitness R f c d hj).hom ≫ Path.map R
      (postnikovCommonClassTransitionToZero R f c d hj ≫
        postnikovZeroClassMap R 1 1 (f.app j).hom)).hom := by
  let z : SquareZero.algebra (postnikovCommonClassBase R f c d)
      (postnikovCommonClassTransitionLayer R f c d hj) ⟶
      postnikovZeroClassTarget R (B.obj j).obj 1 1 :=
    postnikovCommonClassTransitionToZero R f c d hj ≫ postnikovZeroClassMap R 1 1 (f.app j).hom
  have hh := congrArg (fun t => t ≫ (Path.map R z).hom)
    (postnikovCommonClassFixedCompatibility_linear R f c d e)
  simpa only [z, add_comp, sub_comp, ← Mon.comp_hom', Category.assoc,
    Path.diagonal_naturality, postnikovCommonClassFixedTransition_zero_right] using hh

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
