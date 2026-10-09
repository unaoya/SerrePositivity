module

public import SerrePositivity.HomologicalAlgebra.ConeLength
public import SerrePositivity.HomologicalAlgebra.KProjectiveLift
public import SerrePositivity.HomologicalAlgebra.FreeTerms
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.RingTheory.LocalRing.Module

/-!
# 最上段の切り詰め（Lemma 3.5b の準備、段階 4）

局所環 `R` 上、項が有限自由で `1` 次以上が零の複体 `Q` について、`H^0(Q) = 0` なら
`0` 次以上が零の複体 `Q'` で、項が有限自由、`-1` 次より下の項は `Q` と同じものと
ホモトピー同値になる。`Q'` は標準的な切り詰め `τ^{≤ -1} Q` で、`-1` 次の項は
`d : Q^{-1} → Q^0` の核（分裂全射の核なので射影的、局所環上なので自由）。
`Q' → Q` は K 射影的な複体の間の擬同型なのでホモトピー同値（Mathlib の
`CochainComplex.IsKProjective.quasiIso_iff`）。
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace SerrePositivity

variable {R : Type u} [CommRing R]

/-- 有限自由加群への全射の核は、局所環上で有限自由。 -/
lemma free_finite_ker_of_surjective [IsLocalRing R] {M N : Type u} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [Module.Free R M] [Module.Finite R M] [Module.Free R N]
    (d : M →ₗ[R] N) (hd : Function.Surjective d) :
    Module.Free R (LinearMap.ker d) ∧ Module.Finite R (LinearMap.ker d) := by
  obtain ⟨s, hs⟩ := Module.projective_lifting_property d LinearMap.id hd
  let p : M →ₗ[R] LinearMap.ker d :=
    LinearMap.codRestrict (LinearMap.ker d) (LinearMap.id - s ∘ₗ d) (fun x ↦ by
      rw [LinearMap.mem_ker, LinearMap.sub_apply, map_sub, LinearMap.id_apply,
        LinearMap.comp_apply, ← LinearMap.comp_apply d s, hs, LinearMap.id_apply, sub_self])
  have H : p ∘ₗ (LinearMap.ker d).subtype = LinearMap.id := by
    ext ⟨x, hx⟩
    simp only [LinearMap.comp_apply, Submodule.subtype_apply, LinearMap.id_apply, p,
      LinearMap.codRestrict_apply, LinearMap.sub_apply, LinearMap.mem_ker.mp hx, map_zero,
      sub_zero]
  have : Module.Projective R (LinearMap.ker d) :=
    Module.Projective.of_split (LinearMap.ker d).subtype p H
  have hp : Function.Surjective p := fun x ↦ ⟨x, LinearMap.congr_fun H x⟩
  have : Module.Finite R (LinearMap.ker d) := Module.Finite.of_surjective p hp
  exact ⟨Module.free_of_flat_of_isLocalRing, this⟩

/-- 自由加群は圏論的に射影的。 -/
lemma projective_of_free {M : ModuleCat.{u} R} (h : Module.Free R M) : Projective M := by
  have : Module.Projective R M := Module.Projective.of_free
  exact M.projective_of_categoryTheory_projective

/-- **最上段の切り詰め**。 -/
theorem exists_homotopyEquiv_truncate [IsLocalRing R] (Q : CochainComplex (ModuleCat.{u} R) ℤ)
    (hfree : ∀ i, Module.Free R (Q.X i)) (hfin : ∀ i, Module.Finite R (Q.X i))
    (htop : ∀ i : ℤ, 0 < i → IsZero (Q.X i)) (h0 : IsZero (Q.homology 0)) :
    ∃ Q' : CochainComplex (ModuleCat.{u} R) ℤ, (∀ i, Module.Free R (Q'.X i)) ∧
      (∀ i, Module.Finite R (Q'.X i)) ∧ (∀ i : ℤ, -1 < i → IsZero (Q'.X i)) ∧
      (∀ i : ℤ, i ≤ -1 → IsZero (Q.X i) → IsZero (Q'.X i)) ∧ Nonempty (HomotopyEquiv Q' Q) := by
  -- `d : Q^{-1} → Q^0` は全射
  have hex : (Q.sc' (-1) 0 1).Exact := by
    rw [← Q.exactAt_iff' (-1) 0 1 (by simp) (by simp),
      HomologicalComplex.exactAt_iff_isZero_homology]
    exact h0
  have hepi : Epi (Q.d (-1) 0) := hex.epi_f ((htop 1 one_pos).eq_of_tgt _ _)
  have hsurj : Function.Surjective (Q.d (-1) 0).hom := (ModuleCat.epi_iff_surjective _).mp hepi
  have := hfree (-1); have := hfin (-1); have := hfree 0
  obtain ⟨hkf, hkfin⟩ := free_finite_ker_of_surjective _ hsurj
  -- `Q.cycles (-1) ≅ ker d`
  let eK : Q.cycles (-1) ≅ ModuleCat.of R (LinearMap.ker (Q.d (-1) 0).hom) :=
    Q.cyclesIsoSc' (-2) (-1) 0 (by simp) (by simp) ≪≫ (Q.sc' (-2) (-1) 0).moduleCatCyclesIso
  set Q' := Q.truncLE (-1) with hQ'
  have hfree' : ∀ i, Module.Free R (Q'.X i) ∧ Module.Finite R (Q'.X i) := by
    intro i
    rcases lt_trichotomy i (-1) with hi | rfl | hi
    · let e := (Q.truncLEXIso (-1) i hi).toLinearEquiv
      have := hfree i; have := hfin i
      exact ⟨Module.Free.of_equiv e.symm, Module.Finite.equiv e.symm⟩
    · let e := (Q.truncLEXIsoCycles (-1) ≪≫ eK).toLinearEquiv
      exact ⟨Module.Free.of_equiv e.symm, Module.Finite.equiv e.symm⟩
    · have h := Q'.isZero_of_isStrictlyLE (-1) i hi
      exact ⟨isZero_moduleCat_free h, isZero_moduleCat_finite h⟩
  -- 擬同型 `Q' → Q`
  have hLE : Q.IsLE (-1) := by
    rw [CochainComplex.isLE_iff]
    intro i hi
    rw [HomologicalComplex.exactAt_iff_isZero_homology]
    rcases (show i = 0 ∨ 0 < i by omega) with rfl | hi
    · exact h0
    · exact isZero_homology_of_isZero_X' (htop i hi)
  have hQle : Q.IsStrictlyLE 0 := by
    rw [CochainComplex.isStrictlyLE_iff]
    exact htop
  have : ∀ n, Projective (Q.X n) := fun n ↦ projective_of_free (hfree n)
  have : ∀ n, Projective (Q'.X n) := fun n ↦ projective_of_free (hfree' n).1
  have : Q.IsKProjective := CochainComplex.isKProjective_of_projective Q 0
  have : Q'.IsKProjective := CochainComplex.isKProjective_of_projective Q' (-1)
  obtain ⟨E, -⟩ := (CochainComplex.IsKProjective.quasiIso_iff (Q.ιTruncLE (-1))).mp inferInstance
  refine ⟨Q', fun i ↦ (hfree' i).1, fun i ↦ (hfree' i).2,
    fun i hi ↦ Q'.isZero_of_isStrictlyLE (-1) i hi,
    fun i hi hz ↦ ?_, ⟨E⟩⟩
  rcases hi.lt_or_eq with hi | rfl
  · exact (Q.truncLEXIso (-1) i hi).isZero_iff.mpr hz
  · exact (Q.truncLEXIsoCycles (-1)).isZero_iff.mpr (IsZero.of_mono (Q.iCycles (-1)) hz)

end SerrePositivity
