module

public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovSuccessorFixedRightDirectFinalComparison
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPathInvertingFunctor
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovClassConnective

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
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovSuccessorClassInverseData
open ProExcision
variable (R : Type u) [CommRing R] {n : ℤ} {hn : 0 ≤ n} {A B : Tower (NonpositiveAlgebra R)} {f : LevelHom A B}
  {j : ℕ} (d : PostnikovSuccessorClassInverseData R hn f j)
  {C : Type v} [Category.{w} C] (L : Mon (Complex R) ⥤ C)

lemma directOriginal_completed_map_eq (hL : InvertsQuasiIsos R L) :
    L.map (d.directOriginalModelMap R) =
    L.map (d.sourceToRightCompletedModel R ≫ d.fixedRightCompletedRelativeToOriginalModel R) :=
  (Path.Witness.map_eq R L hL (d.directOriginalToFixedModelHomotopy R)).trans
    (Path.Witness.map_eq R L hL (d.fixedRightCompletedOriginalModelHomotopy R))

lemma directOriginal_completed_map_eq_of_connective (hC : InvertsConnectiveQuasiIsos R L) :
    L.map (d.directOriginalModelMap R) =
      L.map (d.sourceToRightCompletedModel R ≫ d.fixedRightCompletedRelativeToOriginalModel R) := by
  let hB := postnikovClassModel_isConnective R (B.obj j).obj n hn
  exact (Path.Witness.map_eq_of_connective R L hC hB
    (d.directOriginalToFixedModelHomotopy R)).trans
    (Path.Witness.map_eq_of_connective R L hC hB (d.fixedRightCompletedOriginalModelHomotopy R))

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovSuccessorClassInverseData
