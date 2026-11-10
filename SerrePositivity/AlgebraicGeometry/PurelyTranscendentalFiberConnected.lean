module

public import SerrePositivity.AlgebraicGeometry.AffineFiberComponentBaseChange

/-!
概要：純超越拡大に値を取る点を持つ連結ファイバーは、幾何学的に連結。
方針：任意の体による底変換を剰余体経由で表し、点の値域と体のテンソル積の整性を使う。
規約：ファイバーは剰余体を左に置くテンソル積で表す。
使われ方：相対 Noether 正規化先の指定成分を有限平坦な標識で広げる。
-/

@[expose] public noncomputable section

namespace SerrePositivity.AlgebraicGeometry

open scoped TensorProduct

/--
概要：連結なファイバーが有理関数体に値を取る点を持てば、指定点に写る任意の体への底変換も連結。
方針：体の構造写像を剰余体経由にし、純超越な点を使う連結性の補題を適用する。
規約：変数の個数には制限を置かない。
使われ方：有限標識に沿って幾何学的に整な開部分を構成する。
-/
theorem connectedSpace_tensor_of_rational_point_in_fiber
    {R B ι : Type u} [CommRing R] [CommRing B] [Algebra R B]
    (p : PrimeSpectrum R) [ConnectedSpace (PrimeSpectrum (p.asIdeal.ResidueField ⊗[R] B))]
    (y : p.asIdeal.ResidueField ⊗[R] B →ₐ[p.asIdeal.ResidueField]
      FractionRing (MvPolynomial ι p.asIdeal.ResidueField))
    (L : Type u) [Field L] [Algebra R L]
    (hp : (⊥ : PrimeSpectrum L).comap (algebraMap R L) = p) :
    ConnectedSpace (PrimeSpectrum (L ⊗[R] B)) := by
  let k := p.asIdeal.ResidueField
  have hk : RingHom.ker (algebraMap R L) = p.asIdeal :=
    congrArg PrimeSpectrum.asIdeal hp
  let f : k →+* L := Ideal.ResidueField.lift p.asIdeal (algebraMap R L) hk.ge
    (fun b hb => isUnit_iff_ne_zero.mpr fun h =>
      hb (hk ▸ (show b ∈ RingHom.ker (algebraMap R L) from h)))
  let : Algebra k L := f.toAlgebra
  let : IsScalarTower R k L := IsScalarTower.of_algebraMap_eq fun b =>
    (Ideal.ResidueField.lift_algebraMap p.asIdeal (algebraMap R L) _ _ b).symm
  let T := FractionRing (MvPolynomial ι k)
  let E := k ⊗[R] B
  let : IsDomain (T ⊗[k] L) := isDomain_tensor_fractionRing_mvPolynomial k L ι
  let : ConnectedSpace (PrimeSpectrum (E ⊗[k] L)) := connectedSpace_tensor_of_connected_point y
  let c := (Algebra.TensorProduct.comm k E L).toRingEquiv.trans
    (Algebra.TensorProduct.cancelBaseChange R k L L B).toRingEquiv
  exact (PrimeSpectrum.homeomorphOfRingEquiv c).connectedSpace_iff.mp inferInstance

end SerrePositivity.AlgebraicGeometry
