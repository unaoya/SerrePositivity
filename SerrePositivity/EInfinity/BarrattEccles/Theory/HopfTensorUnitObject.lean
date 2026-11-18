module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.CommutativeAlgebra
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.AlgebraRestriction
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.AlgebraIso
public import SerrePositivity.EInfinity.BarrattEccles.Theory.DiscreteInitial
public import SerrePositivity.EInfinity.BarrattEccles.Theory.ZeroArity
public import SerrePositivity.EInfinity.BarrattEccles.Hopf

/-!
# Hopf テンソルの単位代数

## 概要
BF §1.1.4 の余単位から、テンソル単位の複体にオペラッド代数の構造を与える。

## 方針
単位対象の可換モノイドを余単位で制限する。零入力の余単位が同型なら自由零代数と同型。

## 規約
一般の Hopf オペラッドを扱い、零入力の同型性は始対象性にだけ要求する。

## 使われ方
HA 3.2.4.7 の二項余積の二つの包含に使う、指定された単位代数からの射。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity
open CategoryTheory MonoidalCategory Limits
open DifferentialGraded TensorPowers
open scoped ZeroObject
variable {A : Type u} [CommRing A] {P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A}
attribute [local irreducible] HomologicalComplex.monoidalCategoryStruct
attribute [local implicit_reducible] TensorPowers.power SerrePositivity.SymmetricSequence
  SerrePositivity.SymmetricSequence.level

/-- BF §1.1.4 の余単位に沿ってテンソル単位の可換代数を制限する。 -/
def hopfTensorUnitObject (hP : P.Hopf) : P.Algebra :=
  _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.restrictAlgebraObj hP.counit
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.commutativeAlgebraOfMonoid (𝟙_ (Complex A)))

/-- 零入力の余単位が同型なら、BF §1.1.4 の単位代数は厳密な始対象である。 -/
def hopfTensorUnitIsInitial (hP : P.Hopf)
    (h0 : IsIso (hP.counit.map.app (FiniteBijection.of 0))) :
    IsInitial (hopfTensorUnitObject hP) := by
  letI := h0
  let U := hopfTensorUnitObject hP
  have hU : IsIso (U.action 0) := by
    change IsIso ((hP.counit.map.app (FiniteBijection.of 0) ▷ 𝟙_ (Complex A)) ≫
      (λ_ (𝟙_ (Complex A))).hom ≫ 𝟙 (𝟙_ (Complex A)))
    infer_instance
  let f : P.freeAlgebra (0 : Complex A) ⟶ U := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.liftHom _ 0
  let j := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurι A P.sequence (0 : Complex A) 0
  have hj : IsIso j := BarrattEccles.schurι_zero_isIso A P.sequence
  have he : j ≫ f.hom = U.action 0 := by
    change j ≫ U.schurLift (0 : (0 : Complex A) ⟶ U.carrier) = U.action 0
    rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.ι_schurLift]
    change (𝟙 (P.arity 0) ⊗ₘ 𝟙 (𝟙_ (Complex A))) ≫ U.action 0 = U.action 0
    rw [id_tensorHom, whiskerLeft_id, Category.id_comp]
  have : IsIso (j ≫ f.hom) := by rw [he]; exact hU
  have : IsIso f.hom := IsIso.of_isIso_comp_left j f.hom
  let e : P.freeAlgebra (0 : Complex A) ≅ U :=
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.isoOfCarrierIso (asIso f.hom) f.comm
  have : P.freeAlgebraFunctor.IsLeftAdjoint := P.freeAlgebraAdjunction.isLeftAdjoint
  have hi : IsInitial (P.freeAlgebra (0 : Complex A)) :=
    (isZero_zero (Complex A)).isInitial.isInitialObj P.freeAlgebraFunctor _
  exact hi.ofIso e

/-- BF §1.1.4 の厳密な単位代数から任意の代数への指定射。 -/
def hopfTensorUnitMap (hP : P.Hopf)
    (h0 : IsIso (hP.counit.map.app (FiniteBijection.of 0))) (Y : P.Algebra) :
    hopfTensorUnitObject hP ⟶ Y :=
  (hopfTensorUnitIsInitial hP h0).to Y

end SerrePositivity.EInfinity
