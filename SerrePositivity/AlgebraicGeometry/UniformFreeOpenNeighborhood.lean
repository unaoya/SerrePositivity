module

public import SerrePositivity.AlgebraicGeometry.FreeOpenBaseChange
public import SerrePositivity.AlgebraicGeometry.FreeOpenFiberNeighborhood

/-!
概要：自由化主開を一つ固定し、基底を縮めて全ファイバーと交わらせる。
方針：自由化元が各ファイバーで非零となる基底の主開を取り、局所化した族へ移す。
規約：基底は点の主近傍へ制限する。
使われ方：Stacks 0815 の余核のファイバー台の次元を一つの写像で下げる。
-/

@[expose] public noncomputable section

namespace SerrePositivity.AlgebraicGeometry

open scoped TensorProduct

/--
概要：指定ファイバーに交わる自由化主開は、基底を主近傍に縮めると全ファイバーと交わる自由化主開となる。
方針：基底の主近傍を開写像で選び、自由性とファイバーでの非零性を局所化で保存する。
規約：元の族は平坦で、指定ファイバーは整とする。
使われ方：余核の次元帰納を基底の各主近傍に適用する。
-/
theorem exists_uniform_freeOpen_over_basicOpen
    {R B N : Type*} [CommRing R] [CommRing B] [Algebra R B] [Module.Flat R B]
    [AddCommGroup N] [Module B N]
    (hopen : IsOpenMap (PrimeSpectrum.comap (algebraMap R B))) (p : PrimeSpectrum R)
    [IsDomain (p.asIdeal.Fiber B)] (b : B) (hb : b ∉ p.asIdeal.map (algebraMap R B))
    [Module.Free (Localization.Away b) (Localization.Away b ⊗[B] N)] :
    ∃ a ∉ p.asIdeal, let A := Localization.Away a
      let D := A ⊗[R] B
      letI : Algebra B D := Algebra.TensorProduct.rightAlgebra
      let c := algebraMap B D b
      let L := Localization.Away c
      Module.Free L (L ⊗[D] (D ⊗[B] N)) ∧
        (∀ q : PrimeSpectrum A, algebraMap D (D ⊗[A] q.asIdeal.ResidueField) c ≠ 0) := by
  obtain ⟨a, ha, h⟩ := exists_base_basicOpen_of_nonzero_in_fiber hopen p b
    (fiber_tmul_ne_zero_of_not_mem_map p.asIdeal b hb)
  let A := Localization.Away a
  let D := A ⊗[R] B
  let : Algebra B D := Algebra.TensorProduct.rightAlgebra
  refine ⟨a, ha, free_baseChange_away_of_free b, fun q => ?_⟩
  have hq : a ∉ (q.comap (algebraMap R A)).asIdeal :=
    fun hmem => q.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _
      hmem (IsLocalization.Away.algebraMap_isUnit a))
  have hne := fiber_tmul_ne_zero_after_baseChange (A := A) q b (h _ hq)
  let e := Algebra.TensorProduct.comm A D q.asIdeal.ResidueField
  intro hz
  apply hne
  have he := congrArg e hz
  change e ((algebraMap B D b) ⊗ₜ[A] (1 : q.asIdeal.ResidueField)) = e 0 at he
  rw [map_zero] at he
  exact he

end SerrePositivity.AlgebraicGeometry
