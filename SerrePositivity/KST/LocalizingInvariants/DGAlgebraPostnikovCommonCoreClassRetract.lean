module

public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreRightZeroNaturality
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovZeroClassInverse

/-!
概要：後続段の実係数逆で右 class 像の経路を戻し、A の遷移後の二 class を比較する。
方針：元の係数逆の厳密な左三角形で f の右像を外し、実経路を同じ代数射で後合成する。
規約：係数逆の源段と比較段を一致させる。使われ方：細分後の class 整合。
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

def postnikovCommonRightRetract : postnikovCommonRightClassTarget R hn f c d ⟶
    postnikovZeroClassTarget R (A.obj j).obj n 1 :=
  postnikovCommonRightClassToZero R hn f c d ≫ e.shiftedClassMap R 1

lemma postnikovCommonRightNumerator_retract : postnikovCommonRightClassNumeratorMap R hn f c d ≫
    postnikovCommonRightRetract R hn f c d e = postnikovCommonNumeratorToZero R hn f c d ≫
      postnikovZeroClassMap R n 1 (A.transition hj).hom := by
  rw [postnikovCommonRightRetract, ← Category.assoc, postnikovCommonRightNumerator_zero,
    Category.assoc, e.shiftedClassMap_left]

lemma postnikovCommonRightRetract_projection : postnikovCommonRightRetract R hn f c d e ≫
    SquareZero.projection _ _ = SquareZero.projection _ _ ≫
      (postnikovCommonRightZeroBase R hn f c d ≫ e.base) := by
  rw [postnikovCommonRightRetract, Category.assoc, e.shiftedClassMap_projection,
    ← Category.assoc, postnikovCommonRightClassToZero_projection, Category.assoc]

def postnikovCommonClassRetractTarget := postnikovCommonRightGlueToCell R hn f c d ≫
  postnikovCommonClassTarget R hn f c d ≫ postnikovCommonNumeratorToZero R hn f c d ≫
    postnikovZeroClassMap R n 1 (A.transition hj).hom

def postnikovCommonClassRetractSource := postnikovCommonRightGlueToCell R hn f c d ≫
  postnikovCommonClassSource R hn f c d ≫ postnikovCommonNumeratorToZero R hn f c d ≫
    postnikovZeroClassMap R n 1 (A.transition hj).hom

lemma postnikovCommonRightGlueTarget_retract : postnikovCommonRightGlueTarget R hn f c d ≫
    postnikovCommonRightRetract R hn f c d e = postnikovCommonClassRetractTarget R hn f c d (hj := hj)
    := by
  simp only [postnikovCommonRightGlueTarget, postnikovCommonClassRetractTarget, Category.assoc]
  rw [postnikovCommonRightNumerator_retract]

lemma postnikovCommonRightGlueSource_retract : postnikovCommonRightGlueSource R hn f c d ≫
    postnikovCommonRightRetract R hn f c d e = postnikovCommonClassRetractSource R hn f c d (hj := hj)
    := by
  simp only [postnikovCommonRightGlueSource, postnikovCommonClassRetractSource, Category.assoc]
  rw [postnikovCommonRightNumerator_retract]

/-- 右像の経路と後続段の実係数逆だけから、A の遷移後の二 class の経路を得る。 -/
def postnikovCommonClassRetractWitness : Path.Witness R
    (postnikovCommonClassRetractTarget R hn f c d (hj := hj))
    (postnikovCommonClassRetractSource R hn f c d (hj := hj)) where
  hom := (postnikovCommonRightClassGlueWitness R hn f c d).hom ≫
    Path.map R (postnikovCommonRightRetract R hn f c d e)
  source_eq := by
    rw [Category.assoc, Path.map_source, ← Category.assoc,
      (postnikovCommonRightClassGlueWitness R hn f c d).source_eq,
      postnikovCommonRightGlueTarget_retract]
  target_eq := by
    rw [Category.assoc, Path.map_target, ← Category.assoc,
      (postnikovCommonRightClassGlueWitness R hn f c d).target_eq,
      postnikovCommonRightGlueSource_retract]

lemma postnikovCommonClassRetractWitness_projection :
    (postnikovCommonClassRetractWitness R hn f c d e).hom ≫ Path.map R (SquareZero.projection _ _) =
      postnikovCommonRightZeroGlueProjection R hn f c d ≫
        (postnikovCommonRightZeroBase R hn f c d ≫ e.base) ≫
          Path.diagonal R (postnikov R (A.obj j).obj 0) := by
  change (_ ≫ Path.map R (postnikovCommonRightRetract R hn f c d e)) ≫ _ = _
  rw [Category.assoc, ← Path.map_comp, postnikovCommonRightRetract_projection,
    Path.map_comp, ← Category.assoc, postnikovCommonRightClassGlueWitness_projection,
    Category.assoc, Path.diagonal_naturality]

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovCommonCore
