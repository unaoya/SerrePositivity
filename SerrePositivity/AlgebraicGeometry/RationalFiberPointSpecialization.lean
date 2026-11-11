module

public import SerrePositivity.AlgebraicGeometry.FractionFieldCommonDenominator
public import Mathlib.Algebra.MvPolynomial.Funext
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.FieldTheory.Perfect

/-!
概要：有理関数体に値を取る点を、有限分離拡大に値を取る点に特殊化する。
方針：有限型部分代数の共通分母を取り、その分母が消えない点で評価する。
規約：有限体の上では、評価に使う座標だけを代数閉包から有限段に取る。
使われ方：相対 Noether 正規化で得た純超越な剰余体の点から、有限平坦な標識を選ぶ。
-/

@[expose] public noncomputable section

namespace SerrePositivity.AlgebraicGeometry

private theorem exists_finite_separable_nonzero_aeval
    {k ι : Type u} [Field k] [Finite ι] (p : MvPolynomial ι k) (hp : p ≠ 0) :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra k L) (_ : FiniteDimensional k L)
      (_ : Algebra.IsSeparable k L) (x : ι → L), MvPolynomial.aeval x p ≠ 0 := by
  classical
  rcases finite_or_infinite k with hk | hk
  · let E := AlgebraicClosure k
    let : PerfectField k := inferInstance
    have hp' : MvPolynomial.map (algebraMap k E) p ≠ 0 := by
      exact fun h => hp ((MvPolynomial.map_injective (algebraMap k E) (RingHom.injective _))
        (h.trans (map_zero _).symm))
    have hn : ∃ x : ι → E, MvPolynomial.aeval x p ≠ 0 := by
      by_contra! h
      apply hp'
      apply MvPolynomial.funext
      intro x
      rw [MvPolynomial.eval_map, ← MvPolynomial.aeval_def, h, map_zero]
    obtain ⟨x, hx⟩ := hn
    let L := IntermediateField.adjoin k (Set.range x)
    let : Finite (Set.range x) := (Set.finite_range x).to_subtype
    let : FiniteDimensional k L := IntermediateField.finiteDimensional_adjoin
      (fun z _ => Algebra.IsIntegral.isIntegral z)
    let y : ι → L := fun j => ⟨x j, IntermediateField.subset_adjoin _ _ (Set.mem_range_self j)⟩
    refine ⟨L, inferInstance, inferInstance, inferInstance, inferInstance, y, ?_⟩
    have he : L.val.comp (MvPolynomial.aeval y) = MvPolynomial.aeval x :=
      MvPolynomial.algHom_ext fun j => by simp [y]
    intro h
    apply hx
    rw [← he, AlgHom.comp_apply, h, map_zero]
  · have hn : ∃ x : ι → k, MvPolynomial.aeval x p ≠ 0 := by
      by_contra! h
      apply hp
      apply MvPolynomial.funext
      intro x
      rw [← MvPolynomial.aeval_eq_eval, h, map_zero]
    obtain ⟨x, hx⟩ := hn
    exact ⟨k, inferInstance, inferInstance, inferInstance, inferInstance, x, hx⟩

/--
概要：有限型代数が有限変数の有理関数体に点を持てば、ある有限分離拡大にも点を持つ。
方針：点の像を主局所化に含め、その分母を消さない代数的な座標で評価する。
規約：基底の体が無限なら基底自身の点を使える。
使われ方：純超越な剰余体を持つ正規化先のファイバー内で、有限平坦な標識を作る。
-/
theorem exists_algHom_finite_separable_of_fractionRing_mvPolynomial
    {k ι B : Type u} [Field k] [Finite ι] [CommRing B] [Algebra k B]
    [Algebra.FiniteType k B] (f : B →ₐ[k] FractionRing (MvPolynomial ι k)) :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra k L) (_ : FiniteDimensional k L)
      (_ : Algebra.IsSeparable k L), Nonempty (B →ₐ[k] L) := by
  let P := MvPolynomial ι k
  let K := FractionRing P
  let : Algebra.FiniteType k f.range :=
    Algebra.FiniteType.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  obtain ⟨p, hp, h⟩ := exists_nonzero_le_fractionField_away_of_finiteType (B := P) f.range
  let T := Localization.subalgebra.ofField K (Submonoid.powers p)
    (powers_le_nonZeroDivisors_of_noZeroDivisors hp)
  obtain ⟨L, _, _, _, _, x, hx⟩ := exists_finite_separable_nonzero_aeval p hp
  let ev : T →ₐ[k] L := IsLocalization.Away.liftAlgHom (S := T) p
    (f := MvPolynomial.aeval x) (isUnit_iff_ne_zero.mpr hx)
  exact ⟨L, inferInstance, inferInstance, inferInstance, inferInstance,
    ⟨ev.comp ((Subalgebra.inclusion h).comp f.rangeRestrict)⟩⟩

end SerrePositivity.AlgebraicGeometry
