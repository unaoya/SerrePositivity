module

public import SerrePositivity.Support.PerfectComplex
public import Mathlib.Algebra.Homology.HomotopyCategory
public import Mathlib.Algebra.Category.ModuleCat.Projective

/-!
# From homological support to null homotopies

A bounded complex of projectives on whose homology a scalar vanishes is
annihilated up to homotopy by a power of that scalar. This is proved by
clearing one degree at a time, starting at the upper bound. No localization
or input from Lemma 3.5 is used.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace SerrePositivity
namespace SupportBridge

variable {T : Type u} [CommRing T]

noncomputable abbrev quot : CochainComplex (ModuleCat.{u} T) ℤ ⥤
    HomotopyCategory (ModuleCat.{u} T) (ComplexShape.up ℤ) :=
  HomotopyCategory.quotient _ _

set_option backward.isDefEq.respectTransparency.types false in
/-- Clear the top remaining component of a chain map after multiplying by a
scalar that annihilates homology. The resulting map has the same homotopy
class as the multiplied map. -/
lemma clear_degree (P : CochainComplex (ModuleCat.{u} T) ℤ) (r : T) (k : ℤ)
    [Projective (P.X k)] (f : P ⟶ P)
    (hf : ∀ i, k < i → f.f i = 0)
    (hr : r • 𝟙 (P.homology k) = 0) :
    ∃ g : P ⟶ P, (∀ i, k ≤ i → g.f i = 0) ∧ quot.map g = r • quot.map f := by
  classical
  let S := P.sc' (k - 1) k (k + 1)
  let e : P.homology k ≅ S.homology :=
    P.homologyIsoSc' (k - 1) k (k + 1)
      (by simp [CochainComplex.prev]) (by simp [CochainComplex.next])
  have hrS : r • 𝟙 S.homology = 0 := by
    have hzero (x : P.homology k) : r • x = 0 :=
      congrArg (fun q : P.homology k ⟶ P.homology k ↦ q.hom x) hr
    ext y
    obtain ⟨x, rfl⟩ := e.toLinearEquiv.surjective y
    change r • e.toLinearEquiv x = 0
    rw [← e.toLinearEquiv.map_smul, hzero x, map_zero]
  have hcycle : f.f k ≫ S.g = 0 := by
    change f.f k ≫ P.d k (k + 1) = 0
    rw [f.comm k (k + 1), hf (k + 1) (by omega), comp_zero]
  let u := S.liftCycles (f.f k) hcycle
  let B := ShortComplex.mk S.toCycles S.homologyπ S.toCycles_comp_homologyπ
  have hB : B.Exact := B.exact_of_g_is_cokernel S.homologyIsCokernel
  have hru : (r • u) ≫ S.homologyπ = 0 := by
    calc
      _ = (u ≫ S.homologyπ) ≫ (r • 𝟙 S.homology) := by
        simp [Linear.smul_comp, Linear.comp_smul]
      _ = 0 := by rw [hrS, comp_zero]
  let h := hB.liftFromProjective (r • u) hru
  have hh : h ≫ P.d (k - 1) k = r • f.f k := by
    change h ≫ S.f = r • f.f k
    rw [← S.toCycles_i, ← Category.assoc, hB.liftFromProjective_comp,
      Linear.smul_comp, S.liftCycles_i]
  let H : ∀ i j : ℤ, P.X i ⟶ P.X j := fun i j ↦
    if hi : i = k then
      if hj : j = k - 1 then
        eqToHom (congrArg P.X hi) ≫ h ≫ eqToHom (congrArg P.X hj.symm)
      else 0
    else 0
  let n := Homotopy.nullHomotopicMap H
  have hn : quot.map n = 0 := by
    apply (HomotopyCategory.quotient_map_eq_zero_iff _).mpr
    refine ⟨Homotopy.nullHomotopy H ?_⟩
    intro i j hij
    dsimp [H]
    split_ifs with hi hj
    · exfalso
      apply hij
      change j + 1 = i
      omega
    all_goals rfl
  have hn_f (i : ℤ) : n.f i = P.d i (i + 1) ≫ H (i + 1) i + H i (i - 1) ≫ P.d (i - 1) i :=
    Homotopy.nullHomotopicMap_f (C := P) (D := P)
      (k₂ := i - 1) (k₁ := i) (k₀ := i + 1)
      (by change i - 1 + 1 = i; omega) rfl H
  refine ⟨r • f - n, ?_, ?_⟩
  · intro i hi
    change r • f.f i - n.f i = 0
    rw [hn_f]
    by_cases hik : i = k
    · subst i
      simp [H, hh, show k + 1 ≠ k by omega]
    · have hki : k < i := by omega
      simp [H, hf i hki, hik, show i + 1 ≠ k by omega]
  · rw [Functor.map_sub, Functor.map_smul, hn, sub_zero]

/-- A power of a homology-annihilating scalar is zero in the homotopy category
for a bounded complex of projectives. -/
theorem exists_pow_nullHomotopy_of_homology_annihilated
    (P : CochainComplex (ModuleCat.{u} T) ℤ) (r : T)
    (hproj : ∀ i, Projective (P.X i))
    (hbound : ∃ a b : ℤ, ∀ i, (i < a ∨ b < i) → IsZero (P.X i))
    (hr : ∀ i, r • 𝟙 (P.homology i) = 0) :
    ∃ n : ℕ, Nonempty (Homotopy (r ^ n • 𝟙 P) 0) := by
  obtain ⟨a, b, hab⟩ := hbound
  have step : ∀ n : ℕ, ∃ f : P ⟶ P,
      (∀ i, b - (n : ℤ) < i → f.f i = 0) ∧
        quot.map f = r ^ n • 𝟙 (quot.obj P) := by
    intro n
    induction n with
    | zero =>
      refine ⟨𝟙 P, ?_, by simp⟩
      intro i hi
      exact (hab i (Or.inr (by simpa using hi))).eq_of_src _ _
    | succ n ih =>
      obtain ⟨f, hf, hclass⟩ := ih
      have := hproj (b - (n : ℤ))
      obtain ⟨g, hg, hgc⟩ := clear_degree P r (b - (n : ℤ)) f hf (hr _)
      refine ⟨g, fun i hi ↦ hg i (by push_cast at hi; omega), ?_⟩
      rw [hgc, hclass, ← mul_smul, ← pow_succ']
  obtain ⟨f, hf, hc⟩ := step (b - a + 1).toNat
  have hzero : f = 0 := by
    apply HomologicalComplex.hom_ext
    intro i
    by_cases hi : i < a
    · exact (hab i (Or.inl hi)).eq_of_src _ _
    · exact hf i (by omega)
  refine ⟨(b - a + 1).toNat, ?_⟩
  apply (HomotopyCategory.quotient_map_eq_zero_iff _).mp
  change quot.map (r ^ (b - a + 1).toNat • 𝟙 P) = 0
  rw [Functor.map_smul, CategoryTheory.Functor.map_id, ← hc, hzero, Functor.map_zero]

end SupportBridge

variable {T : Type u} [CommRing T] [IsNoetherianRing T]

/-- The homological support criterion gives the null-homotopy criterion for
a bounded complex of finite projective modules. -/
theorem isSupported_of_homologySupport {e : ℕ} (w : Fin e → T)
    (P : CochainComplex (ModuleCat.{u} T) ℤ)
    (hfinite : ∀ i, Module.Finite T (P.X i)) (hproj : ∀ i, Projective (P.X i))
    (hbound : ∃ a b : ℤ, ∀ i, (i < a ∨ b < i) → IsZero (P.X i))
    (hP : HasHomologySupport (Ideal.span (Set.range w)) P) : IsSupported w P := by
  classical
  obtain ⟨n, hn⟩ := exists_common_pow_annihilator_of_homologySupport _ P hfinite hbound hP
  have each : ∀ j, ∃ v : ℕ, Nonempty (Homotopy (w j ^ v • 𝟙 P) 0) := by
    intro j
    have hw : w j ∈ Ideal.span (Set.range w) := Ideal.subset_span (Set.mem_range_self j)
    have hwN : w j ^ n ∈ (Ideal.span (Set.range w)) ^ n := Ideal.pow_mem_pow hw n
    have hr : ∀ i, w j ^ n • 𝟙 (P.homology i) = 0 := by
      intro i
      ext x
      exact @hn i x ⟨w j ^ n, hwN⟩
    obtain ⟨m, hm⟩ := SupportBridge.exists_pow_nullHomotopy_of_homology_annihilated
      P (w j ^ n) hproj hbound hr
    exact ⟨n * m, by simpa only [pow_mul] using hm⟩
  choose v hv using each
  refine ⟨Finset.univ.sup v, fun j ↦ ?_⟩
  have hj : v j ≤ Finset.univ.sup v := Finset.le_sup (Finset.mem_univ j)
  have h := (hv j).some.smul (w j ^ (Finset.univ.sup v - v j))
  rw [smul_zero, ← mul_smul, ← pow_add, Nat.sub_add_cancel hj] at h
  exact ⟨h⟩

/-- On bounded finite projective complexes, the two notions of support agree. -/
theorem isSupported_iff_homologySupport {e : ℕ} (w : Fin e → T)
    (P : CochainComplex (ModuleCat.{u} T) ℤ)
    (hfinite : ∀ i, Module.Finite T (P.X i)) (hproj : ∀ i, Projective (P.X i))
    (hbound : ∃ a b : ℤ, ∀ i, (i < a ∨ b < i) → IsZero (P.X i)) :
    IsSupported w P ↔ HasHomologySupport (Ideal.span (Set.range w)) P := by
  constructor
  · intro h
    exact (homologySupport_iff_le_radical_annihilator _ P hfinite).mpr
      (h.le_radical_annihilator)
  · exact isSupported_of_homologySupport w P hfinite hproj hbound

/-- Package a bounded finite free complex with homologically defined support
in the exact form required by Lemma 3.5. -/
theorem isPerfectSupported_of_homologySupport {e : ℕ} (w : Fin e → T)
    (P : CochainComplex (ModuleCat.{u} T) ℤ)
    (hfinite : ∀ i, Module.Finite T (P.X i)) (hfree : ∀ i, Module.Free T (P.X i))
    (hbound : ∃ a b : ℤ, ∀ i, (i < a ∨ b < i) → IsZero (P.X i))
    (hP : HasHomologySupport (Ideal.span (Set.range w)) P) : IsPerfectSupported w P where
  bounded := hbound
  free := hfree
  finite := hfinite
  supported := isSupported_of_homologySupport w P hfinite
    (fun i ↦ by have := hfree i; infer_instance) hbound hP

end SerrePositivity
