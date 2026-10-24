module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraCellFourthRefinement
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraCellPathSourceMap
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonClassStandardZeroGlue
public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonRightClassifyingBaseChange

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreRightComparisonRefinement
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreSpecialization

/-!
概要：元の Γ 源から、classifying 比較と二因子分解比較の両方の源へ写す。
方針：既存の非正次数射影を前合成し、各比較の元の P への射影を計算する。
規約：新しい共通源を選ばない。使われ方：右三角形の経路を同じ細分上へ移す。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
open ProExcision
variable (R : Type u) [CommRing R] {A B : Tower (NonpositiveAlgebra R)} (f : LevelHom A B)
  {i m : ℕ} {hi : i ≤ m} (c : NonpositiveInverseRoof R (f.map (postnikovFunctor R 1)) i m hi)
  (d : PostnikovCommonLayerInverse R f c)

def postnikovCommonRightToClassifying : postnikovCommonClassStandardGlueSource R f c d ⟶
    cellResolution R (postnikovCommonRightCellSource R f c d) :=
  PostnikovCommonCore.postnikovCommonRightToClassifying
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c)

lemma postnikovCommonRightToClassifying_projection :
    postnikovCommonRightToClassifying R f c d ≫
      postnikovCommonRightClassifyingProjection R f c d =
        postnikovCommonClassStandardGlueProjection R f c d :=
  PostnikovCommonCore.postnikovCommonRightToClassifying_projection
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c)

def postnikovCommonRightToFactorization : postnikovCommonClassStandardGlueSource R f c d ⟶
    cellResolution R (cellResolution R (cellResolution R
      (cellResolution R (postnikovCommonClassBase R f c d)))) :=
  PostnikovCommonCore.postnikovCommonRightToFactorization
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c)

lemma postnikovCommonRightToFactorization_projection :
    postnikovCommonRightToFactorization R f c d ≫
      postnikovCellFactorizationProjection R (postnikovCommonClassBase R f c d) =
        postnikovCommonClassStandardGlueProjection R f c d :=
  PostnikovCommonCore.postnikovCommonRightToFactorization_projection
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c)

lemma postnikovCommonRightToClassifying_quasiIso :
    QuasiIso (postnikovCommonRightToClassifying R f c d).hom :=
  PostnikovCommonCore.postnikovCommonRightToClassifying_quasiIso
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c)

lemma postnikovCommonRightToFactorization_quasiIso :
    QuasiIso (postnikovCommonRightToFactorization R f c d).hom :=
  PostnikovCommonCore.postnikovCommonRightToFactorization_quasiIso
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
