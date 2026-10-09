module

public import SerrePositivity.CommutativeAlgebra.FiniteLength
public import SerrePositivity.HomologicalAlgebra.FreeTerms
public import SerrePositivity.PerfectComplex.NormalizedEuler
public import SerrePositivity.PerfectComplex.K0

/-!
# Ordinary Euler evaluation on supported perfect complexes

Over a Noetherian ring `T`, a perfect complex supported on the zero locus of an
ideal with Artinian quotient has finite-length homology. Its ordinary Euler
evaluation descends to the supported Grothendieck group. No normalized length
or choice of a normalization base is involved.

Homotopy invariance and mapping-cone additivity of `chiOrd` are the special case
`NormalizedLength.ordinary` of the statements in `NormalizedEuler.lean`
(`chiOrd_eq_lambdaEuler_ordinary`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace SerrePositivity

variable {T : Type u} [CommRing T] [IsNoetherianRing T]

/-- Supported perfect complexes have finite-length homology whenever the
quotient by the support ideal is Artinian. -/
theorem homology_finiteLength_of_isPerfectSupported {e : ℕ} {w : Fin e → T}
    [IsArtinianRing (T ⧸ Ideal.span (Set.range w))]
    {P : CochainComplex (ModuleCat.{u} T) ℤ} (hP : IsPerfectSupported w P) (i : ℤ) :
    IsFiniteLength T (P.homology i) := by
  have := hP.finite i
  have := homology_moduleFinite P i
  exact isFiniteLength_of_le_radical_annihilator _ _ (hP.supported.le_radical_annihilator i)

omit [IsNoetherianRing T] in
/-- Ordinary Euler evaluation is invariant under homotopy equivalence. -/
lemma chiOrd_eq_of_homotopyEquiv {P Q : CochainComplex (ModuleCat.{u} T) ℤ}
    (h : HomotopyEquiv P Q) : chiOrd P = chiOrd Q := by
  rw [chiOrd_eq_lambdaEuler_ordinary, chiOrd_eq_lambdaEuler_ordinary]
  exact lambdaEuler_eq_of_homotopyEquiv _ h

omit [IsNoetherianRing T] in
/-- The ordinary Euler evaluation is additive on a mapping-cone triangle when
the homology is bounded and has finite length. This is `lambdaEuler_cone` for
`NormalizedLength.ordinary`; the torsion hypotheses hold trivially for `J = ⊥`. -/
theorem chiOrd_cone {P Q : CochainComplex (ModuleCat.{u} T) ℤ} (f : P ⟶ Q)
    (hQ : ∃ a b : ℤ, ∀ i, (i < a ∨ b < i) → IsZero (Q.X i))
    (hC : ∃ a b : ℤ, ∀ i, (i < a ∨ b < i) → IsZero ((Cone.cone f).X i))
    (lP : ∀ i, Module.length T (P.homology i) ≠ ⊤)
    (lQ : ∀ i, Module.length T (Q.homology i) ≠ ⊤)
    (lC : ∀ i, Module.length T ((Cone.cone f).homology i) ≠ ⊤) :
    chiOrd (Cone.cone f) = chiOrd Q - chiOrd P := by
  simp only [chiOrd_eq_lambdaEuler_ordinary]
  exact lambdaEuler_cone _ f hQ hC (fun _ ↦ IsPowTorsion.bot) (fun _ ↦ IsPowTorsion.bot)
    (fun _ ↦ IsPowTorsion.bot) (fun i ↦ ENat.toENNReal_ne_top.mpr (lP i))
    (fun i ↦ ENat.toENNReal_ne_top.mpr (lQ i)) (fun i ↦ ENat.toENNReal_ne_top.mpr (lC i))

/-- Ordinary Euler evaluation as a homomorphism on the supported Grothendieck
group over a Noetherian ring with Artinian support quotient. -/
noncomputable def chiOrdHom {e : ℕ} (w : Fin e → T)
    [IsArtinianRing (T ⧸ Ideal.span (Set.range w))] : K0Supported T w →+ ℝ :=
  K0.lift (fun P ↦ chiOrd P.1)
    (fun _ _ h ↦ chiOrd_eq_of_homotopyEquiv h)
    (fun P Q f hc ↦ chiOrd_cone f Q.2.bounded hc.bounded
      (fun i ↦ Module.length_ne_top_iff.mpr (homology_finiteLength_of_isPerfectSupported P.2 i))
      (fun i ↦ Module.length_ne_top_iff.mpr (homology_finiteLength_of_isPerfectSupported Q.2 i))
      (fun i ↦ Module.length_ne_top_iff.mpr (homology_finiteLength_of_isPerfectSupported hc i)))

@[simp]
lemma chiOrdHom_mk {e : ℕ} (w : Fin e → T)
    [IsArtinianRing (T ⧸ Ideal.span (Set.range w))] (P : PerfSupp T w) :
    chiOrdHom w (K0.mk P) = chiOrd P.1 := K0.lift_mk _ _ _ _

end SerrePositivity
