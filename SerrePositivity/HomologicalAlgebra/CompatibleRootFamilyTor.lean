module

public import SerrePositivity.HomologicalAlgebra.CompatibleRootFiniteFamilyTor
public import SerrePositivity.HomologicalAlgebra.FiniteSupQuotientColimit
public import SerrePositivity.HomologicalAlgebra.TorExactColimits
public import SerrePositivity.CommutativeAlgebra.CompatibleRoot
/-! # Arbitrary compatible-root family quotients are Tor-independent from perfect coefficients

Finite-subset quotient maps and exact colimit preservation retain the original Tor.
There is no finite-generation, flatness, or regular-sequence hypothesis.
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {p : ℕ} [Fact p.Prime] {σ : Type u}
  {R : Type u} [CommRing R] [CharP R p] [PerfectRing R p]

/-- The supremum of any root family gives vanishing in every positive Tor degree. -/
lemma compatibleRootSupQuotient_tor_subsingleton (κ : σ → ℕ → R)
    (hκ : ∀ a n, κ a (n + 1) ^ p = κ a n)
    (C : Type u) [CommRing C] [Algebra R C] [PerfectRing C p]
    (i : ℕ) (hi : 0 < i) :
    Subsingleton (TorModule R i (R ⧸ ⨆ a, compatibleRootIdeal (κ a)) C) := by
  classical
  let I := fun a => compatibleRootIdeal (κ a)
  let D := finiteSupQuotientDiagram I
  let G := (Tor (ModuleCat.{u} R) i).obj (ModuleCat.of R C)
  letI := moduleCat_hasExactFinsetColimits (R := R) σ
  letI := tor_preservesExactColimits (J := Finset σ) (ModuleCat.of R C) i
  have hs (s : Finset σ) : IsZero (G.obj (D.obj s)) := by
    letI := compatibleRootFiniteFamilyQuotient_tor_subsingleton s R κ hκ C i hi
    have ht : Subsingleton (TorModule R i C (R ⧸ s.sup I)) :=
      (torModuleComm (R := R) i C (R ⧸ s.sup I)).injective.subsingleton
    apply ModuleCat.isZero_iff_subsingleton.mpr
    exact ht
  have hz : IsZero (colimit (D ⋙ G)) := by
    apply (IsZero.iff_id_eq_zero _).mpr
    apply colimit.hom_ext
    intro s
    exact (hs s).eq_of_src _ _
  have hf : IsZero (G.obj (colimit D)) := hz.of_iso (preservesColimitIso G D)
  have hq : IsZero (G.obj (ModuleCat.of R (R ⧸ ⨆ a, I a))) :=
    hf.of_iso (G.mapIso (finiteSupQuotientColimitIso I).symm)
  letI := ModuleCat.subsingleton_of_isZero hq
  exact (torModuleComm (R := R) i (R ⧸ ⨆ a, I a) C).injective.subsingleton

/-- The actual root-family ideal quotient has the same Tor vanishing. -/
lemma compatibleRootFamilyQuotient_tor_subsingleton (κ : σ → ℕ → R)
    (hκ : ∀ a n, κ a (n + 1) ^ p = κ a n)
    (C : Type u) [CommRing C] [Algebra R C] [PerfectRing C p]
    (i : ℕ) (hi : 0 < i) :
    Subsingleton (TorModule R i (R ⧸ compatibleRootFamilyIdeal κ) C) := by
  rw [compatibleRootFamilyIdeal_eq_iSup]
  exact compatibleRootSupQuotient_tor_subsingleton κ hκ C i hi
end SerrePositivity
