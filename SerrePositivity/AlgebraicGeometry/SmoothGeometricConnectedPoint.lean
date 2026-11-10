module

public import SerrePositivity.AlgebraicGeometry.SmoothConnectedDomain
public import SerrePositivity.AlgebraicGeometry.TensorConnectedPoint
import Mathlib.RingTheory.TensorProduct.Maps

/-!
概要：体上の滑らかな連結アフィンに有理点があれば、任意の体拡大で整になる。
方針：有理点から体拡大後の連結性を示し、滑らかさから整性を得る。
規約：有理点は体への代数準同型で表す。
使われ方：切断を通る生成ファイバーの連結成分に幾何学的整性を与える。
-/

@[expose] public noncomputable section

namespace SerrePositivity.AlgebraicGeometry

open scoped TensorProduct

/--
概要：体上の滑らかな連結アフィンが有理点を持てば、任意の拡大体への底変換は整域。
方針：有理点を使って連結性を底変換し、滑らかな連結代数の整性を適用する。
規約：拡大体の次数は制限しない。
使われ方：Stacks 055N の切断を通る生成ファイバー成分。
-/
theorem isDomain_tensor_of_connected_smooth_of_section
    {k B L : Type*} [Field k] [Field L] [Algebra k L]
    [CommRing B] [Algebra k B] [Algebra.Smooth k B] [ConnectedSpace (PrimeSpectrum B)]
    (s : B →ₐ[k] k) : IsDomain (L ⊗[k] B) := by
  let e := Algebra.TensorProduct.lid k L
  let : ConnectedSpace (PrimeSpectrum (k ⊗[k] L)) :=
    (PrimeSpectrum.homeomorphOfRingEquiv e.toRingEquiv).connectedSpace_iff.mpr inferInstance
  let : ConnectedSpace (PrimeSpectrum (B ⊗[k] L)) := connectedSpace_tensor_of_connected_point s
  let h := PrimeSpectrum.homeomorphOfRingEquiv (Algebra.TensorProduct.comm k B L).toRingEquiv
  let : ConnectedSpace (PrimeSpectrum (L ⊗[k] B)) := h.connectedSpace_iff.mp inferInstance
  exact isDomain_of_connected_smooth_over_field (k := L)

end SerrePositivity.AlgebraicGeometry
