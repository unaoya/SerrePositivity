module

public import SerrePositivity.EInfinity.BarrattEccles.Theory.HopfTensorFunctor
public import SerrePositivity.EInfinity.BarrattEccles.Theory.HopfTensorUnitObject
public import SerrePositivity.EInfinity.BarrattEccles.Theory.HopfTensorUnitPowers

/-!
# Hopf テンソル代数の左右の単位同型

## 概要
BF §1.1.4 の余単位則から、台の左右の単位子を代数の同型へ持ち上げる。

## 方針
二列の作用の余単位の縮約と、単位因子のテンソル冪の比較を合成する。

## 規約
零入力での余単位の同型性は不要で、任意の Hopf オペラッドを扱う。

## 使われ方
HA 3.2.4.7 の二項余積からテンソルへの比較の二つの包含。
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

/-- BF §1.1.4 の右余単位から得る代数の右単位同型。 -/
def hopfTensorRightUnitor (hP : P.Hopf) (X : P.Algebra) :
    hopfTensorAlgebra hP X (hopfTensorUnitObject hP) ≅ X := by
  refine _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.isoOfCarrierIso (ρ_ X.carrier) ?_
  intro n
  have h := tensorActionRightCounit (hP.diagonalComponent n)
    (hP.counit.map.app (FiniteBijection.of n))
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerSeparation X.carrier (𝟙_ (Complex A)) n).hom (X.action n)
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.powerProduct (𝟙_ (Complex A)) n) (hP.right_counit n)
  rw [tensorPowerSeparation_rightUnit] at h
  rw [id_tensorHom]
  exact h

/-- BF §1.1.4 の左余単位から得る代数の左単位同型。 -/
def hopfTensorLeftUnitor (hP : P.Hopf) (X : P.Algebra) :
    hopfTensorAlgebra hP (hopfTensorUnitObject hP) X ≅ X := by
  refine _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.isoOfCarrierIso (λ_ X.carrier) ?_
  intro n
  have h := tensorActionLeftCounit (hP.diagonalComponent n)
    (hP.counit.map.app (FiniteBijection.of n))
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerSeparation (𝟙_ (Complex A)) X.carrier n).hom (X.action n)
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.powerProduct (𝟙_ (Complex A)) n) (hP.left_counit n)
  rw [tensorPowerSeparation_leftUnit] at h
  rw [id_tensorHom]
  exact h

end SerrePositivity.EInfinity
