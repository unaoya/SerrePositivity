module

public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonRightGammaZeroClass
public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovTwoFixedRightDirectSourcePath

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovSuccessorRightGammaEndpoints

/-!
概要：Γ 上の W source 経路の両端を、元の class 模型で使う cell 射に照合する。
方針：同じ Γ の一重 cell 射と塔の合成式を使い、分母側の元の source を回収する。
規約：source 経路を選び直さない。使われ方：動く底の模型経路の端点同定。
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

lemma postnikovCommonRightGammaToSource_toCell :
    postnikovCommonRightGammaToSource R f c d ≫
      cellPathNonpositiveToCell R (postnikovCommonClassBase R f c d) =
        postnikovCommonClassCompatibilityToCell R f c d :=
  PostnikovCommonCore.postnikovCommonRightGammaToSource_toCell
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c)

lemma postnikovCommonRightGamma_comparison {C : Mon (Complex R)}
    (b : postnikovCommonClassBase R f c d ⟶ C) :
    postnikovCommonRightGammaToSource R f c d ≫ cellPathNonpositiveComparison R b =
      postnikovCommonClassCompatibilityToCell R f c d ≫ cellResolutionMap R b :=
  PostnikovCommonCore.postnikovCommonRightGamma_comparison
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (C := C) (b := b)

variable {j : ℕ} (hj : j ≤ i)

lemma postnikovCommonRightGammaSourceWitness_source :
    (postnikovCommonRightGammaSourceWitness R f c d hj).hom ≫
      Path.source R (postnikovPerturbedExtension R (B.obj j).obj 1 (by omega)) =
    (postnikovCommonClassCompatibilityToCell R f c d ≫
      cellResolutionMap R (postnikovCommonRightBase R f c d ≫
        postnikovMap R (B.transition hj).hom 1)) ≫
          postnikovCellLift R (B.obj j).obj 1 (by omega) :=
  PostnikovCommonCore.postnikovCommonRightGammaSourceWitness_source
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj)

lemma postnikovCommonRightGammaSourceWitness_target :
    (postnikovCommonRightGammaSourceWitness R f c d hj).hom ≫
      Path.target R (postnikovPerturbedExtension R (B.obj j).obj 1 (by omega)) =
    (postnikovCommonClassCompatibilityToCell R f c d ≫
      cellResolutionMap R (postnikovCommonRightDenBase R f c d ≫
        postnikovMap R (B.transition hj).hom 1)) ≫
          postnikovCellLift R (B.obj j).obj 1 (by omega) :=
  PostnikovCommonCore.postnikovCommonRightGammaSourceWitness_target
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj)

lemma postnikovCommonClassRightDenominatorBase_composite :
    postnikovCommonClassRightDenominatorBase R f c d hj =
      postnikovCommonRightDenBase R f c d ≫ postnikovMap R (B.transition hj).hom 1 :=
  PostnikovCommonCore.postnikovCommonClassRightDenominatorBase_composite
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra

namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovTwoClassInverseData
open ProExcision
variable (R : Type u) [CommRing R] {A B : Tower (NonpositiveAlgebra R)} {f : LevelHom A B}
  {j : ℕ} (d : PostnikovTwoClassInverseData R f j)

lemma rightGammaSourceWitness_target :
    (postnikovCommonRightGammaSourceWitness R f d.baseInverse d.layerInverse d.target_le).hom ≫
      Path.target R (postnikovPerturbedExtension R (B.obj j).obj 1 (by omega)) =
        d.fixedRightCompletedNativeSource R :=
  PostnikovSuccessorClassInverseData.rightGammaSourceWitness_target
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovTwoClassInverseData
