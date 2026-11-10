module

public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import Mathlib.RingTheory.Ideal.IdempotentFG
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.RingTheory.Flat.Basic

/-!
概要：体上の連結なアフィンの底変換を、一つの点の底変換から判定する。
方針：テンソル積の冪等元の係数が生成する有限生成イデアルも冪等であることを使う。
規約：基底変更の体の拡大次数に制限を置かない。
使われ方：切断を通るファイバー成分の底変換。
-/

@[expose] public noncomputable section

namespace SerrePositivity.AlgebraicGeometry

open scoped TensorProduct

private theorem tensor_repr_map
    {k B C L ι : Type*} [Field k] [CommRing B] [Algebra k B] [CommRing C] [Algebra k C]
    [CommRing L] [Algebra k L] (b : Module.Basis ι k L) (f : B →ₐ[k] C)
    (x : B ⊗[k] L) (i : ι) :
    (b.baseChange C).repr (Algebra.TensorProduct.map f (AlgHom.id k L) x) i =
      f ((b.baseChange B).repr x i) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a l =>
    simp [Algebra.smul_def]
  | add x y hx hy => simp [hx, hy]

private theorem tensor_mem_mapped_ideal_iff
    {k B L ι : Type*} [Field k] [CommRing B] [Algebra k B] [CommRing L] [Algebra k L]
    (b : Module.Basis ι k L) (I : Ideal B) (x : B ⊗[k] L) :
    x ∈ I.map (Algebra.TensorProduct.includeLeft : B →ₐ[k] B ⊗[k] L).toRingHom ↔
      ∀ i, (b.baseChange B).repr x i ∈ I := by
  let f := Ideal.Quotient.mkₐ k I
  have he := Algebra.TensorProduct.rTensor_ker (R := k) (S := k) f (C := L) Ideal.Quotient.mk_surjective
  change RingHom.ker (Algebra.TensorProduct.map f (AlgHom.id k L)).toRingHom =
    (RingHom.ker f.toRingHom).map
      (Algebra.TensorProduct.includeLeft : B →ₐ[k] B ⊗[k] L).toRingHom at he
  have hf : RingHom.ker f.toRingHom = I := Ideal.mk_ker
  rw [hf] at he
  rw [← he, RingHom.mem_ker]
  change Algebra.TensorProduct.map f (AlgHom.id k L) x = 0 ↔ _
  constructor
  · intro h i
    have hi := tensor_repr_map b f x i
    rw [h, map_zero, Finsupp.zero_apply] at hi
    exact Ideal.Quotient.eq_zero_iff_mem.mp hi.symm
  · intro h
    apply (b.baseChange (B ⧸ I)).repr.injective
    ext i
    rw [tensor_repr_map, map_zero, Finsupp.zero_apply]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (h i)

private theorem tensor_idempotent_eq_zero_of_map_eq_zero
    {k B T L : Type*} [Field k] [CommRing B] [Algebra k B] [CommRing T] [Algebra k T]
    [CommRing L] [Algebra k L] [Nontrivial T] [PreconnectedSpace (PrimeSpectrum B)]
    (y : B →ₐ[k] T) (e : B ⊗[k] L) (he : IsIdempotentElem e)
    (hy : Algebra.TensorProduct.map y (AlgHom.id k L) e = 0) : e = 0 := by
  classical
  let b := Module.Free.chooseBasis k L
  let c := (b.baseChange B).repr e
  let I := Ideal.span (c '' (c.support : Set (Module.Free.ChooseBasisIndex k L)))
  let j : B →ₐ[k] B ⊗[k] L := Algebra.TensorProduct.includeLeft
  have hcoeff (i : Module.Free.ChooseBasisIndex k L) : c i ∈ I := by
    by_cases hi : i ∈ c.support
    · exact Ideal.subset_span ⟨i, hi, rfl⟩
    · rw [Finsupp.notMem_support_iff.mp hi]
      exact I.zero_mem
  have heI : e ∈ I.map j.toRingHom := (tensor_mem_mapped_ideal_iff b I e).mpr hcoeff
  have hesq : e ∈ (I * I).map j.toRingHom := by
    rw [Ideal.map_mul, ← he.eq]
    exact Ideal.mul_mem_mul heI heI
  have hI : IsIdempotentElem I := by
    apply le_antisymm Ideal.mul_le_left
    apply Ideal.span_le.mpr
    rintro _ ⟨i, _, rfl⟩
    exact (tensor_mem_mapped_ideal_iff b (I * I) e).mp hesq i
  obtain ⟨a, ha, hIa⟩ := (I.isIdempotentElem_iff_of_fg
    (Submodule.fg_span (c.support.finite_toSet.image c))).mp hI
  have hker : I ≤ RingHom.ker y.toRingHom := by
    apply Ideal.span_le.mpr
    rintro _ ⟨i, _, rfl⟩
    have h := tensor_repr_map b y e i
    rw [hy, map_zero, Finsupp.zero_apply] at h
    exact h.symm
  have ha0 : a = 0 := by
    have ho : IsClopen (PrimeSpectrum.basicOpen a : Set (PrimeSpectrum B)) :=
      PrimeSpectrum.isClopen_iff.mpr ⟨a, ha, rfl⟩
    rcases isClopen_iff.mp ho with h | h
    · exact PrimeSpectrum.basicOpen_injOn_isIdempotentElem ha (by simp [IsIdempotentElem])
        (SetLike.ext' (by simpa using h))
    · have ha1 : a = 1 := PrimeSpectrum.basicOpen_injOn_isIdempotentElem ha
        (by simp [IsIdempotentElem]) (SetLike.ext' (by simpa using h))
      have hamem : a ∈ I := hIa ▸ Submodule.mem_span_singleton_self a
      have hz : y a = 0 := hker hamem
      rw [ha1, map_one] at hz
      exact (one_ne_zero hz).elim
  have hI0 : I = ⊥ := by rw [hIa, ha0, Submodule.span_zero_singleton]
  apply (b.baseChange B).repr.injective
  ext i
  have hi := hcoeff i
  simpa [hI0] using hi

/--
概要：連結な体上のアフィンに、体拡大後も連結な点の源から写像があれば、
アフィン全体もその体拡大後に連結。
方針：拡大上の冪等元とその補冪等元を、点の源への制限で判定する。
規約：点の源は非零の基底代数でよい。
使われ方：有理点を通る連結成分の幾何学的連結性。
-/
theorem connectedSpace_tensor_of_connected_point
    {k B T L : Type*} [Field k] [CommRing B] [Algebra k B] [CommRing T] [Algebra k T]
    [Field L] [Algebra k L] [Nontrivial T] [ConnectedSpace (PrimeSpectrum B)]
    [ConnectedSpace (PrimeSpectrum (T ⊗[k] L))] (y : B →ₐ[k] T) :
    ConnectedSpace (PrimeSpectrum (B ⊗[k] L)) := by
  let f := Algebra.TensorProduct.map y (AlgHom.id k L)
  let : Nontrivial (T ⊗[k] L) := PrimeSpectrum.nonempty_iff_nontrivial.mp inferInstance
  let : Nontrivial (B ⊗[k] L) := f.domain_nontrivial
  refine connectedSpace_iff_clopen.mpr ⟨PrimeSpectrum.nonempty_iff_nontrivial.mpr inferInstance, ?_⟩
  intro s hs
  obtain ⟨e, he, rfl⟩ := PrimeSpectrum.isClopen_iff.mp hs
  have he' : IsIdempotentElem (f e) := he.map f
  have ho : IsClopen (PrimeSpectrum.basicOpen (f e) : Set (PrimeSpectrum (T ⊗[k] L))) :=
    PrimeSpectrum.isClopen_iff.mpr ⟨f e, he', rfl⟩
  rcases isClopen_iff.mp ho with h | h
  · have hz : f e = 0 := PrimeSpectrum.basicOpen_injOn_isIdempotentElem he'
      (by simp [IsIdempotentElem]) (SetLike.ext' (by simpa using h))
    rw [tensor_idempotent_eq_zero_of_map_eq_zero y e he hz, PrimeSpectrum.basicOpen_zero]
    exact Or.inl rfl
  · have h1 : f e = 1 := PrimeSpectrum.basicOpen_injOn_isIdempotentElem he'
      (by simp [IsIdempotentElem]) (SetLike.ext' (by simpa using h))
    have hz : f (1 - e) = 0 := by rw [map_sub, map_one, h1, sub_self]
    have hzero := tensor_idempotent_eq_zero_of_map_eq_zero y (1 - e) he.one_sub hz
    rw [(sub_eq_zero.mp hzero).symm, PrimeSpectrum.basicOpen_one]
    exact Or.inr rfl

end SerrePositivity.AlgebraicGeometry
