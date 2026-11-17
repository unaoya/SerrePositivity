module

public import Mathlib.RingTheory.Nullstellensatz
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
概要：代数閉体上の非零な有限型代数に、係数を保つ点を供給する。
方針：有限個の変数の多項式表示の核を極大イデアルに含め、弱Nullstellensatzの評価を降ろす。
規約：係数と値域の宇宙を保ち、点の存在をNonemptyで述べる。
使われ方：2iのQ01、BM18 Proposition 4.8 (3),(4) の有限表示模型の剰余体上の点。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.AlgebraicGeometry.ArcRouteB

/-- 計画Q01：非零な有限型代数の代数閉係数体への点。 -/
theorem nonempty_algHom_of_isAlgClosed (k C : Type u) [Field k]
    [IsAlgClosed k] [CommRing C] [Nontrivial C] [Algebra k C]
    [Algebra.FiniteType k C] : Nonempty (C →ₐ[k] k) := by
  classical
  obtain ⟨s, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial.mp
    (inferInstance : Algebra.FiniteType k C)
  obtain ⟨m, hm, hkm⟩ := Ideal.exists_le_maximal (RingHom.ker f.toRingHom)
    (RingHom.ker_ne_top f.toRingHom)
  obtain ⟨x, hx⟩ := MvPolynomial.eq_vanishingIdeal_singleton_of_isMaximal k hm
  let ev : MvPolynomial {y // y ∈ s} k →ₐ[k] k := MvPolynomial.aeval x
  have hker : RingHom.ker f.toRingHom ≤ RingHom.ker ev.toRingHom := by
    intro z hz
    have hz' : z ∈ MvPolynomial.vanishingIdeal k {x} := hx ▸ hkm hz
    exact hz' x (Set.mem_singleton x)
  exact ⟨AlgHom.liftOfSurjective f hf ev hker⟩

end SerrePositivity.AlgebraicGeometry.ArcRouteB
