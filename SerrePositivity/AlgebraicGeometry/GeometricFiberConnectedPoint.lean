module

public import SerrePositivity.AlgebraicGeometry.AffineSectionComponentLocus

/-!
概要：幾何学的に連結な指定ファイバーは、アフィン底変換後に指定点の上でも連結。
方針：底変換先の点の剰余体で二段階のテンソル積を一段階にまとめる。
規約：指定ファイバーの幾何学的連結性は、その点に写るすべての体について与える。
使われ方：有限標識の自己ファイバー積の指定ファイバー上で二つの切断を比較する。
-/

@[expose] public noncomputable section

namespace SerrePositivity.AlgebraicGeometry

open scoped TensorProduct

/--
概要：幾何学的に連結な指定ファイバーは、任意のアフィン底変換後、その点の上の各ファイバーで連結。
方針：底変換先の剰余体で評価し、連結なスペクトルの像として位相ファイバーを表す。
規約：ファイバーはスペクトル写像の一点の逆像で表す。
使われ方：Stacks 057I で、標識の自己ファイバー積上の切断が同じ成分を選ぶこと。
-/
theorem isConnected_specTensor_fiber_of_geometricFiberAt
    {A B V : Type u} [CommRing A] [CommRing B] [CommRing V] [Algebra A B] [Algebra A V]
    (a : PrimeSpectrum A)
    (h : ∀ (K : Type u) [Field K] [Algebra A K],
      (⊥ : PrimeSpectrum K).comap (algebraMap A K) = a →
        ConnectedSpace (PrimeSpectrum (K ⊗[A] B)))
    (p : PrimeSpectrum V) (hp : p.comap (algebraMap A V) = a) :
    IsConnected (PrimeSpectrum.comap (algebraMap V (V ⊗[A] B)) ⁻¹' {p}) := by
  let K := p.asIdeal.ResidueField
  have hpK : (⊥ : PrimeSpectrum K).comap (algebraMap V K) = p :=
    PrimeSpectrum.ext (Ideal.ker_algebraMap_residueField (I := p.asIdeal))
  have haK : (⊥ : PrimeSpectrum K).comap (algebraMap A K) = a := by
    rw [IsScalarTower.algebraMap_eq A V K, PrimeSpectrum.comap_comp_apply, hpK, hp]
  let : ConnectedSpace (PrimeSpectrum (K ⊗[A] B)) := h K haK
  let e := Algebra.TensorProduct.cancelBaseChange A V K K B
  let : ConnectedSpace (PrimeSpectrum (K ⊗[V] (V ⊗[A] B))) :=
    (PrimeSpectrum.homeomorphOfRingEquiv e.toRingEquiv).connectedSpace_iff.mpr inferInstance
  rw [← range_comap_includeRight_residueField (B := V ⊗[A] B) p, ← Set.image_univ]
  exact isConnected_univ.image _ (PrimeSpectrum.continuous_comap _).continuousOn

end SerrePositivity.AlgebraicGeometry
