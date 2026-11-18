module

public import SerrePositivity.EInfinity.BarrattEccles.Theory.HopfTensorUnit
public import SerrePositivity.EInfinity.BarrattEccles.Theory.HopfTensorInsertion
public import SerrePositivity.EInfinity.BarrattEccles.Theory.TensorActionAssembly
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.AlgebraFirstComposition

/-!
# Hopf オペラッド代数のテンソル

## 概要
BF §1.1.4 の Hopf 対角から、HA 3.2.4.7 の比較先のテンソル代数を構成する。

## 方針
二列分離の単位・等変性・先頭代入との比較を、元の二つの代数の公理へ帰着する。

## 規約
台は元の二つの非有界複体のテンソルであり、cofibrancy は構成に要求しない。

## 使われ方
厳密な二項余積からテンソルへの比較射と、台の導来テンソルとの自然比較。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity
open CategoryTheory MonoidalCategory
open DifferentialGraded TensorPowers
variable {A : Type u} [CommRing A] {P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A}
attribute [local irreducible] HomologicalComplex.monoidalCategoryStruct
attribute [local implicit_reducible] TensorPowers.power SerrePositivity.SymmetricSequence
  SerrePositivity.SymmetricSequence.level

/-- BF §1.1.4 のテンソル作用は、先頭位置での部分合成を保つ。 -/
lemma hopfTensorAction_comp_zero (hP : P.Hopf) (X Y : P.Algebra) (m n : ℕ) :
    (P.comp m n 0 ▷ power (X.carrier ⊗ Y.carrier) (m + n)) ≫
      hopfTensorAction hP X Y (m + n) =
      (α_ (P.arity (m + 1)) (P.arity n)
        (power (X.carrier ⊗ Y.carrier) (m + n))).hom ≫
        (P.arity (m + 1) ◁ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorInsertionAction (X.carrier ⊗ Y.carrier)
          (P.arity n) m n 0 (hopfTensorAction hP X Y n)) ≫
            hopfTensorAction hP X Y (m + 1) := by
  have hi := tensorInsertionAction_separation_zero X.carrier Y.carrier
    (P.arity n) (P.arity n) (P.arity n) m n (hP.diagonalComponent n) (X.action n) (Y.action n)
  exact tensorActionAssembly_composition
    (hP.diagonalComponent (m + 1)) (hP.diagonalComponent n) (hP.diagonalComponent (m + n))
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerSeparation X.carrier Y.carrier (m + n)).hom
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerSeparation X.carrier Y.carrier (m + 1)).hom
    (P.comp m n 0) (P.comp m n 0) (P.comp m n 0)
    (X.action (m + n)) (Y.action (m + n)) (X.action (m + 1)) (Y.action (m + 1))
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorInsertionAction (X.carrier ⊗ Y.carrier) (P.arity n) m n 0 (hopfTensorAction hP X Y n))
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorInsertionAction X.carrier (P.arity n) m n 0 (X.action n))
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorInsertionAction Y.carrier (P.arity n) m n 0 (Y.action n))
    (hP.diagonal.comp m n 0) (X.comp_action m n 0) (Y.comp_action m n 0) hi

/-- BF §1.1.4 の Hopf 対角で二つの代数のテンソルを代数にする。 -/
def hopfTensorAlgebra (hP : P.Hopf) (X Y : P.Algebra) : P.Algebra :=
  _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.ofFirstComposition P (X.carrier ⊗ Y.carrier) (hopfTensorAction hP X Y)
    (hopfTensorAction_equivariance hP X Y) (hopfTensorAction_comp_zero hP X Y)
    (hopfTensorAction_unit hP X Y)

end SerrePositivity.EInfinity
