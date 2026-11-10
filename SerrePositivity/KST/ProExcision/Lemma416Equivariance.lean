module
public import SerrePositivity.KST.ProExcision.Lemma416EquivariantData
public import SerrePositivity.KST.ProExcision.EquivariantHomotopyOperations
public import SerrePositivity.KST.ProExcision.ConstructionA5Equivariant

/-!
# Lemma 4.16 の実帰納ホモトピーの全行列同変性

概要：非可換な実ブロック群で構成した全 m の帰納ホモトピーは全行列作用と可換。
方針：因子内の入力の同変性、μ 版 A.5、固定元 u の A.6、線形な連結と相殺を合成する。
規約：KST Lemma 4.16 の非可換再記述、A.5 の右辺の augmentation 補正。
使われ方：相対ホモロジー零化への入力。単体環への関手的移送は別工程。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
universe u
namespace SerrePositivity.KST.ProExcision
open CategoryTheory
variable {R : Type u} [Ring R]

/-- 概要：実帰納段階は入力の全行列同変性を保つ。
方針：同変な A.5 と A.6 の区間射を同じ線形な連結・相殺へ適用する。
規約：KST Lemma 4.16、因子内の帰納仮定を使う。
使われ方：全 m の帰納ホモトピーの行列同変性。 -/
lemma lemma416HomotopyStep_equivariant (n m : ℕ) (J : TwoSidedIdeal R) (a : J)
    (h : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.LinearizedMHomotopy (groupLinearizedMap (lastRightColumnHom n m J (a : R)))
      (groupLinearizedMap (1 : Multiplicative (Fin n → J) →* triangularBlockGroup n (m + 1) J)) m)
    (hh : LinearizedCylinderEquivariant
      (discreteNerveAction (MonCat.of (Matrix (Fin n) (Fin n) R))
        (MonCat.of (Multiplicative (Fin n → J))) (idealMatrixAction n J))
      (discreteNerveAction (MonCat.of (Matrix (Fin n) (Fin n) R))
        (MonCat.of (triangularBlockGroup n (m + 1) J)) (triangularBlockMatrixAction n (m + 1) J)) h.h) :
    LinearizedCylinderEquivariant
      (discreteNerveAction (MonCat.of (Matrix (Fin n) (Fin n) R))
        (MonCat.of (Multiplicative (Fin n → J))) (idealMatrixAction n J))
      (discreteNerveAction (MonCat.of (Matrix (Fin n) (Fin n) R))
        (MonCat.of (triangularBlockGroup n (m + 2) J)) (triangularBlockMatrixAction n (m + 2) J))
      (lemma416HomotopyStep n m J a h).h := by
  let d := lemma416EquivariantGroupData n m J (a : R)
  let inp : ConstructionA5Input d m 0 :=
    { first := h
      second := groupZeroMHomotopy (MonoidHom.id (Multiplicative (Fin n → J)))
      first_equivariant := hh
      second_equivariant := groupZeroMHomotopy_equivariant (idealMatrixAction n J) (idealMatrixAction n J)
        (MonoidHom.id _) (by intro M v; rfl) }
  have hA := constructionA5_equivariant d m 0 inp
  have hC := groupConjugationMHomotopy_equivariant (idealMatrixAction n J)
    (triangularBlockMatrixAction n (m + 2) J) (auxiliaryBlockColumnHom n m J)
    (auxiliaryBlockColumnHom_equivariant n m J) (auxiliaryBlockUnit n m J a)
    (auxiliaryBlockUnit_fixed n m J a) (m + 1)
  have hψ := groupLinearizedMap_equivariant (idealMatrixAction n J)
    (triangularBlockMatrixAction n (m + 2) J) (auxiliaryBlockColumnHom n m J)
    (auxiliaryBlockColumnHom_equivariant n m J)
  have hφ := groupLinearizedMap_equivariant (idealMatrixAction n J)
    (triangularBlockMatrixAction n (m + 2) J) (lastRightColumnHom n (m + 1) J (a : R))
    (lastRightColumnHom_equivariant n (m + 1) J (a : R))
  have hp := groupLinearizedMap_equivariant (idealMatrixAction n J)
    (triangularBlockMatrixAction n (m + 2) J) d.toGroupProductData.product d.product_equivariant
  have heq := (hψ.add hφ).constant.sub ((hC.add hA).sub hp.constant)
  exact heq

/-- 概要：全 m の実右乗法の帰納ホモトピーは全行列作用に同変。
方針：零次の定数区間の同変性から帰納段階の保存を繰り返す。
規約：KST Lemma 4.16 の非可換な離散環上の全行列同変版。
使われ方：A.4 の同変ホモトピーによる相対零化。単体環への移送は別途示す。 -/
lemma lemma416Homotopy_equivariant (n : ℕ) (J : TwoSidedIdeal R) (a : J) (m : ℕ) :
    LinearizedCylinderEquivariant
      (discreteNerveAction (MonCat.of (Matrix (Fin n) (Fin n) R))
        (MonCat.of (Multiplicative (Fin n → J))) (idealMatrixAction n J))
      (discreteNerveAction (MonCat.of (Matrix (Fin n) (Fin n) R))
        (MonCat.of (triangularBlockGroup n (m + 1) J)) (triangularBlockMatrixAction n (m + 1) J))
      (lemma416Homotopy n J a m).h := by
  induction m with
  | zero =>
    exact groupZeroMHomotopy_equivariant (idealMatrixAction n J) (triangularBlockMatrixAction n 1 J)
      (lastRightColumnHom n 0 J (a : R)) (lastRightColumnHom_equivariant n 0 J (a : R))
  | succ m ih =>
    exact lemma416HomotopyStep_equivariant n m J a (lemma416Homotopy n J a m) ih

end SerrePositivity.KST.ProExcision
