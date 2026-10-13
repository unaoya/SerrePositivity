module

public import SerrePositivity.CommutativeAlgebra.HilbertSamuelBasic
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! # 環同型による Hilbert–Samuel 重複度の不変性

環同型でイデアルを移したとき、冪による商加群は半線形同値になる。
部分加群束の順序同型により Samuel 関数の長さを比較し、多項式の一意性から
選択した多項式と重複度の一致を得る。多項式が存在しない場合の零の分岐も移すので、
Noether 性、局所性、準素性の追加仮定は不要である。
-/

@[expose] public section
universe u
namespace SerrePositivity.HilbertSamuel

variable {R S : Type u} [CommRing R] [CommRing S]

/-- 環同型に対応するイデアルの商の、基底環に関する加群長は等しい。 -/
theorem length_quotient_map_ringEquiv (e : R ≃+* S) (I : Ideal R) :
    Module.length S (S ⧸ I.map e.toRingHom) = Module.length R (R ⧸ I) := by
  let E := Ideal.quotientEquiv I (I.map e.toRingHom) e rfl
  let f : (R ⧸ I) →ₛₗ[e.toRingHom] (S ⧸ I.map e.toRingHom) :=
    { toFun := E
      map_add' := E.map_add
      map_smul' := fun r x ↦ by
        obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
        change E (Ideal.Quotient.mk I (r * x)) =
          Ideal.Quotient.mk (I.map e.toRingHom) (e r * e x)
        change Ideal.Quotient.mk (I.map e.toRingHom) (e (r * x)) =
          Ideal.Quotient.mk (I.map e.toRingHom) (e r * e x)
        rw [map_mul] }
  let : RingHomSurjective e.toRingHom := ⟨e.surjective⟩
  apply WithBot.coe_injective
  rw [Module.coe_length, Module.coe_length]
  exact (Order.krullDim_eq_of_orderIso
    (Submodule.orderIsoMapComapOfBijective f E.bijective)).symm

/-- 環自体の Samuel 関数は環同型とイデアルの像によって変わらない。 -/
theorem samuelFunction_map_ringEquiv (e : R ≃+* S) (I : Ideal R) (n : ℕ) :
    samuelFunction S (I.map e.toRingHom) S n = samuelFunction R I R n := by
  have hR : (I ^ n • ⊤ : Submodule R R) = I ^ n :=
    (Ideal.smul_eq_mul _ _).trans (Ideal.mul_top _)
  have hS : ((I.map e.toRingHom) ^ n • ⊤ : Submodule S S) = (I.map e.toRingHom) ^ n :=
    (Ideal.smul_eq_mul _ _).trans (Ideal.mul_top _)
  unfold samuelFunction
  rw [hR, hS, ← Ideal.map_pow]
  exact length_quotient_map_ringEquiv e (I ^ n)

/-- 環自体の Samuel 多項式である条件は、環同型に沿ってイデアルを移しても同じ。 -/
theorem isSamuelPoly_map_ringEquiv_iff (e : R ≃+* S) (I : Ideal R) (P : Polynomial ℚ) :
    IsSamuelPoly S (I.map e.toRingHom) S P ↔ IsSamuelPoly R I R P := by
  simp only [IsSamuelPoly, samuelFunction_map_ringEquiv]

/-- 選択した Samuel 多項式は環同型で変わらない。存在しない場合も両側で零となる。 -/
theorem poly_map_ringEquiv (e : R ≃+* S) (I : Ideal R) :
    poly S (I.map e.toRingHom) S = poly R I R := by
  classical
  by_cases h : ∃ P : Polynomial ℚ, IsSamuelPoly R I R P
  · exact poly_eq S ((isSamuelPoly_map_ringEquiv_iff e I _).mpr (isSamuelPoly_poly R h))
  · have hS : ¬ ∃ P : Polynomial ℚ, IsSamuelPoly S (I.map e.toRingHom) S P := by
      rintro ⟨P, hP⟩
      exact h ⟨P, (isSamuelPoly_map_ringEquiv_iff e I P).mp hP⟩
    simp only [poly, h, hS, dite_false]

/-- 環自体の Hilbert–Samuel 重複度は、環同型と対応するイデアルについて一致する。 -/
theorem multiplicity_map_ringEquiv (e : R ≃+* S) (I : Ideal R) :
    multiplicity S (I.map e.toRingHom) S = multiplicity R I R := by
  simp only [multiplicity, Module.supportDim_self_eq_ringKrullDim]
  rw [← ringKrullDim_eq_of_ringEquiv e, poly_map_ringEquiv]

/-- 生成元の族を環同型で移したイデアルについて、環自体の重複度は一致する。 -/
theorem multiplicity_span_map_ringEquiv (e : R ≃+* S) {ι : Type*} (x : ι → R) :
    multiplicity S (Ideal.span (Set.range (e ∘ x))) S =
      multiplicity R (Ideal.span (Set.range x)) R := by
  rw [Set.range_comp, ← Ideal.map_span]
  exact multiplicity_map_ringEquiv e (Ideal.span (Set.range x))

end SerrePositivity.HilbertSamuel
