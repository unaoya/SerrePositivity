module

public import SerrePositivity.AlgebraicGeometry.BoundaryFlatBaseChange
public import SerrePositivity.AlgebraicGeometry.IteratedPureTransform
public import SerrePositivity.AlgebraicGeometry.PureTransformCongr
public import SerrePositivity.AlgebraicGeometry.PureTransformScalarRestriction
public import SerrePositivity.AlgebraicGeometry.TensorAlgebraBoundaryTorsion

/-!
概要：基底変更後に純変換を取っても、境界外の平坦性は保たれる。
方針：境界を可逆にした環では、純変換の前後の二段テンソルを比較する。
規約：中間の係数変更は任意とする。
使われ方：Stacks 0815 の自由化 blowup の後で、余核の次元帰納に境界外の平坦性を渡す。
-/

@[expose] public noncomputable section

namespace SerrePositivity.AlgebraicGeometry

open scoped TensorProduct

/--
概要：境界元の像が可逆な底変換では、純変換の商を取る前後の底変換は同型。
方針：二段の純変換の同型から、可逆元のねじれが零であることを使って外側の商を除く。
規約：元の境界ねじれは一様な冪で消えると仮定する。
使われ方：純変換の境界外の平坦性を元の加群に戻す。
-/
def baseChangePureTransformEquivOfIsUnit
    {R S M : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M] (a : R) (n : ℕ)
    (hn : ∀ x ∈ boundaryTorsion a M, a ^ n • x = 0)
    (ha : IsUnit (algebraMap R S a)) :
    (S ⊗[R] modulePureTransform a M) ≃ₗ[S] S ⊗[R] M := by
  let b := algebraMap R S a
  let N := S ⊗[R] M
  let P := S ⊗[R] modulePureTransform a M
  let eN := (boundaryTorsion b N).quotEquivOfEqBot
    (boundaryTorsion_eq_bot_of_isSMulRegular b N (ha.isSMulRegular N))
  let eP := (boundaryTorsion b P).quotEquivOfEqBot
    (boundaryTorsion_eq_bot_of_isSMulRegular b P (ha.isSMulRegular P))
  let e := modulePureTransform_baseChange_pureTransformEquivOfBound (A := S) a n hn
  exact eP.symm.trans (e.symm.trans eN)

/--
概要：有限型代数上の有限加群の純変換は、境界外で元の加群が平坦なら、境界外で平坦。
方針：基底変更後の境界ねじれの指数を求め、境界を可逆にした環上で元の加群と比較する。
規約：純変換を底変換代数上の有限加群として表す。
使われ方：自由化 blowup の各標準チャートにおける余核の次元帰納。
-/
theorem flat_tensorAlgebra_pureTransform_away_of_boundary_flat
    {R B C M : Type*} [CommRing R] [CommRing B] [CommRing C] [Algebra R B] [Algebra R C]
    [IsNoetherianRing C] [Algebra.FiniteType R B]
    [AddCommGroup M] [Module R M] [Module B M] [IsScalarTower R B M] [Module.Finite B M]
    (a : R) [Module.Flat (Localization.Away a) (Localization.Away a ⊗[R] M)] :
    let D := C ⊗[R] B
    letI : Algebra B D := Algebra.TensorProduct.rightAlgebra
    let b := algebraMap R C a
    let L := Localization.Away b
    Module.Flat L (L ⊗[C] modulePureTransform (algebraMap C D b) (D ⊗[B] M)) := by
  let D := C ⊗[R] B
  let : Algebra B D := Algebra.TensorProduct.rightAlgebra
  let b := algebraMap R C a
  let L := Localization.Away b
  let N := D ⊗[B] M
  let e := tensorAlgebraBaseChangeEquiv R B C M
  obtain ⟨n, hn⟩ := tensorAlgebraModule_boundaryTorsion_bounded R B C M b
  let : Module.Flat L (L ⊗[R] M) := flat_tensor_away_of_boundary_flat R C M a
  let : Module.Flat L (L ⊗[C] (C ⊗[R] M)) :=
    Module.Flat.of_linearEquiv (TensorProduct.AlgebraTensorModule.cancelBaseChange R C L L M)
  let e₀ := (modulePureTransformScalarRestrictionEquiv (B := D) (M := N) b).symm
  let e₁ := modulePureTransformCongr b e
  let e₂ := baseChangePureTransformEquivOfIsUnit (S := L) b n hn
    (IsLocalization.Away.algebraMap_isUnit b)
  exact Module.Flat.of_linearEquiv (((e₀.trans e₁).baseChange C L _ _).trans e₂)

end SerrePositivity.AlgebraicGeometry
