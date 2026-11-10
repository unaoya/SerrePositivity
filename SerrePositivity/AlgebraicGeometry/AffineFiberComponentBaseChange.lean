module

public import SerrePositivity.AlgebraicGeometry.TensorConnectedPoint
public import SerrePositivity.AlgebraicGeometry.NoetherianFiberComponent
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Spectrum.Prime.Noetherian
public import Mathlib.RingTheory.TensorProduct.MvPolynomial

/-!
概要：指定点を通るアフィンファイバーの連結成分を体拡大と比較する。
方針：連結成分を冪等元の主開で表し、局所化と底変換の比較を使う。
規約：指定点の体を拡大したテンソル積が連結である場合を扱う。
使われ方：切断を通る成分の底変換と、純超越な剰余体を持つ成分の選択。
-/

@[expose] public noncomputable section

namespace SerrePositivity.AlgebraicGeometry

open scoped TensorProduct nonZeroDivisors

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/--
概要：有理関数体を基底体の任意の拡大体とテンソルして得る環は整域。
方針：拡大体上の多変数多項式環を、元の多項式環の非零元で局所化する。
規約：変数の集合に有限性を仮定しない。
使われ方：純超越な剰余体を持つ点の体拡大後の連結性。
-/
theorem isDomain_tensor_fractionRing_mvPolynomial
    (k L σ : Type*) [Field k] [Field L] [Algebra k L] :
    IsDomain (FractionRing (MvPolynomial σ k) ⊗[k] L) := by
  let P := MvPolynomial σ k
  let F := FractionRing P
  let D := L ⊗[k] P
  let T := L ⊗[k] F
  let : IsDomain D := (MvPolynomial.algebraTensorAlgEquiv k L (σ := σ)).toRingEquiv.isDomain
  have hinj : Function.Injective (algebraMap P D) :=
    Algebra.TensorProduct.includeRight_injective (R := k) (A := L)
      (RingHom.injective (algebraMap k L))
  let : Algebra D T :=
    (Algebra.TensorProduct.map (AlgHom.id k L) (IsScalarTower.toAlgHom k P F)).toAlgebra
  let : IsScalarTower L D T := IsScalarTower.of_algebraMap_eq fun x => by
    change x ⊗ₜ[k] (1 : F) =
      Algebra.TensorProduct.map (AlgHom.id k L) (IsScalarTower.toAlgHom k P F)
        (x ⊗ₜ[k] (1 : P))
    simp
  let : IsLocalization ((nonZeroDivisors P).map (algebraMap P D)) T := by
    change IsLocalization ((nonZeroDivisors P).map
      (Algebra.TensorProduct.includeRight : P →ₐ[k] D)) T
    exact IsLocalization.tensorProduct_tensorProduct_right k L (nonZeroDivisors P) F
      (by ext <;> simp [RingHom.algebraMap_toAlgebra])
  let : IsDomain T := IsLocalization.isDomain_of_le_nonZeroDivisors T
    (map_le_nonZeroDivisors_of_injective (algebraMap P D) hinj le_rfl)
  exact (Algebra.TensorProduct.comm k F L).toRingEquiv.isDomain

/--
概要：体拡大後も連結な点の体を持つ指定点について、その連結成分の逆像は、
体拡大後の指定点を通る連結成分に等しい。
方針：元の成分を冪等元の主開で表し、局所化した代数の底変換が連結であることを示す。
規約：元のアフィン環は Noether とする。
使われ方：Stacks 37.29.2 のアフィンの場合のファイバー成分の比較。
-/
theorem preimage_connectedComponent_eq_of_tensor_connected_point
    {k L B F : Type*} [Field k] [Field L] [Algebra k L] [Field F] [Algebra k F]
    [CommRing B] [Algebra k B] [IsNoetherianRing B]
    [ConnectedSpace (PrimeSpectrum (F ⊗[k] L))]
    (y : B →ₐ[k] F) (q : PrimeSpectrum (L ⊗[k] B))
    (hq : q.comap (Algebra.TensorProduct.includeRight (R := k)).toRingHom =
      (⊥ : PrimeSpectrum F).comap y.toRingHom) :
    PrimeSpectrum.comap (Algebra.TensorProduct.includeRight (R := k)).toRingHom ⁻¹'
      connectedComponent ((⊥ : PrimeSpectrum F).comap y.toRingHom) =
      connectedComponent q := by
  let p := (⊥ : PrimeSpectrum F).comap y.toRingHom
  let j : B →ₐ[k] L ⊗[k] B := Algebra.TensorProduct.includeRight
  obtain ⟨e, he, hC⟩ := PrimeSpectrum.isClopen_iff.mp
    (isClopen_connectedComponent_of_noetherianSpace p)
  have hep : e ∉ p.asIdeal := by
    apply (PrimeSpectrum.mem_basicOpen _ _).mp
    change p ∈ (PrimeSpectrum.basicOpen e : Set (PrimeSpectrum B))
    rw [← hC]
    exact mem_connectedComponent
  have hye : IsUnit (y e) := isUnit_iff_ne_zero.mpr fun h => hep (Ideal.mem_bot.mpr h)
  let B' := Localization.Away e
  let y' : B' →ₐ[k] F := IsLocalization.Away.liftAlgHom (S := B') e (f := y) hye
  let i := PrimeSpectrum.comap (algebraMap B B')
  have hr : Set.range i = connectedComponent p :=
    (PrimeSpectrum.localization_away_comap_range B' e).trans hC.symm
  let : ConnectedSpace (PrimeSpectrum B') := by
    let h := (PrimeSpectrum.localization_away_isOpenEmbedding B' e).isEmbedding.toHomeomorph
    rw [h.connectedSpace_iff, ← isConnected_iff_connectedSpace, hr]
    exact isConnected_connectedComponent
  let : ConnectedSpace (PrimeSpectrum (B' ⊗[k] L)) := connectedSpace_tensor_of_connected_point y'
  let D := L ⊗[k] B
  let D' := Localization.Away (j e)
  let f : B' ⊗[k] L ≃+* D' :=
    (Algebra.TensorProduct.comm k B' L).toRingEquiv.trans
      (IsLocalization.Away.tensorProductEquivTMulRight k L e B').toRingEquiv
  let : ConnectedSpace (PrimeSpectrum D') :=
    (PrimeSpectrum.homeomorphOfRingEquiv f).connectedSpace_iff.mp inferInstance
  have hpre : PrimeSpectrum.comap j.toRingHom ⁻¹' connectedComponent p =
      (PrimeSpectrum.basicOpen (j e) : Set (PrimeSpectrum D)) := by
    rw [hC]
    rfl
  change PrimeSpectrum.comap j.toRingHom ⁻¹' connectedComponent p = _
  rw [hpre]
  have hq' : q ∈ (PrimeSpectrum.basicOpen (j e) : Set (PrimeSpectrum D)) := by
    rw [← hpre]
    change q.comap j.toRingHom ∈ connectedComponent p
    rw [hq]
    exact mem_connectedComponent
  have hcl : IsClopen (PrimeSpectrum.basicOpen (j e) : Set (PrimeSpectrum D)) :=
    PrimeSpectrum.isClopen_iff.mpr ⟨j e, he.map j, rfl⟩
  refine Set.Subset.antisymm ?_ (hcl.connectedComponent_subset hq')
  have hconnected : IsConnected (PrimeSpectrum.basicOpen (j e) : Set (PrimeSpectrum D)) := by
    rw [← PrimeSpectrum.localization_away_comap_range D' (j e), ← Set.image_univ]
    exact isConnected_univ.image _ (PrimeSpectrum.continuous_comap _).continuousOn
  exact hconnected.subset_connectedComponent hq'

end SerrePositivity.AlgebraicGeometry
