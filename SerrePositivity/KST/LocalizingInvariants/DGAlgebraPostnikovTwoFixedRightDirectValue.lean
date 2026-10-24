module

public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovTwoFixedRightDirectFinalComparison
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPathInvertingFunctor
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovClassConnective

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovSuccessorFixedRightDirectValue

/-!
概要：元の直接 B 遷移の模型合成と、接合 fixed 合成の像を準同型局所化で比較する。
方針：元の二つの乗法的模型経路を同じ関手で写し、射の等式を合成する。
規約：任意経路の連結可能性を仮定しない。使われ方：右逆三角形の直接側の値。
-/

@[expose] public section
noncomputable section
universe u v w
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovTwoClassInverseData
open ProExcision
variable (R : Type u) [CommRing R] {A B : Tower (NonpositiveAlgebra R)} {f : LevelHom A B}
  {j : ℕ} (d : PostnikovTwoClassInverseData R f j)
  {C : Type v} [Category.{w} C] (L : Mon (Complex R) ⥤ C)

lemma directOriginal_completed_map_eq (hL : InvertsQuasiIsos R L) :
    L.map (d.directOriginalModelMap R) =
    L.map (d.sourceToRightCompletedModel R ≫ d.fixedRightCompletedRelativeToOriginalModel R) :=
  PostnikovSuccessorClassInverseData.directOriginal_completed_map_eq
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R) (C := C) (L := L) (hL := hL)

lemma directOriginal_completed_map_eq_of_connective (hC : InvertsConnectiveQuasiIsos R L) :
    L.map (d.directOriginalModelMap R) =
      L.map (d.sourceToRightCompletedModel R ≫ d.fixedRightCompletedRelativeToOriginalModel R) :=
  PostnikovSuccessorClassInverseData.directOriginal_completed_map_eq_of_connective
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R) (C := C) (L := L) (hC := hC)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovTwoClassInverseData
