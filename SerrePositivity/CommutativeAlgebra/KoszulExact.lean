module

public import SerrePositivity.CommutativeAlgebra.Koszul
public import SerrePositivity.HomologicalAlgebra.ConeLES
public import SerrePositivity.HomologicalAlgebra.FreeTerms
public import Mathlib.Algebra.Homology.HomotopyCategory.HomologicalFunctor
public import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated
public import Mathlib.Algebra.Homology.HomotopyCategory.ShiftSequence
public import Mathlib.Algebra.Homology.ShortComplex.Linear
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Homology.SingleHomology
public import Mathlib.RingTheory.Regular.RegularSequence

/-!
# Koszul 複体の完全性

正則列 `x` の Koszul 複体 `K(x; R)` は `R/(x)` の自由分解である：
`H^i(K(x)) = 0 (i ≠ 0)`、`H^0(K(x)) ≅ R/(x)`。

証明は `n` に関する帰納法。`K(x₀,…,xₙ) = Cone(xₙ • 𝟙 : K' → K')`（`K' = K(x₀,…,xₙ₋₁)`）で、
写像錐の三角 `K' → K' → Cone → K'[1]` にホモロジー関手（homological functor）を当てた
長完全列を使う。`xₙ` が `H^0(K') ≅ R/(x₀,…,xₙ₋₁)` 上で正則なので `H^{-1}(Cone) = 0`、
`H^0(Cone) = H^0(K')/xₙ = R/(x)`。

写像錐の長完全列 `Cone.exact₁₂₃`（`HomologicalAlgebra/ConeLES.lean`）を `φ = smulId a K` に適用する。
-/

@[expose] public section

universe u

open CategoryTheory Limits Pretriangulated

namespace SerrePositivity

variable {R : Type u} [CommRing R]

/-! ## Koszul 複体の完全性 -/

lemma koszulComplex_zero (x : Fin 0 → R) :
    koszulComplex x =
      (HomologicalComplex.single (ModuleCat.{u} R) (ComplexShape.up ℤ) 0).obj (ModuleCat.of R R) :=
  rfl

lemma koszulComplex_succ {n : ℕ} (x : Fin (n + 1) → R) :
    koszulComplex x =
      CochainComplex.mappingCone (smulId (x (Fin.last n)) (koszulComplex (Fin.init x))) :=
  rfl

/-- `K(x; R)` が `R/(x)` の分解であること：`H^i = 0 (i ≠ 0)`、`H^0 ≅ R/(x)`。 -/
structure IsKoszulResolution {n : ℕ} (x : Fin n → R) : Prop where
  /-- `i ≠ 0` でホモロジーは零。 -/
  isZero : ∀ i : ℤ, i ≠ 0 → IsZero ((koszulComplex x).homology i)
  /-- `H^0 ≅ R/(x)`。 -/
  equiv : Nonempty ((koszulComplex x).homology 0 ≃ₗ[R] R ⧸ Ideal.span (Set.range x))

/-- `n = 0`：`K(∅) = R` は `R/(0)` の分解。 -/
lemma isKoszulResolution_zero (x : Fin 0 → R) : IsKoszulResolution x where
  isZero i hi := by
    rw [koszulComplex_zero]
    exact HomologicalComplex.isZero_single_obj_homology _ _ _ _ hi
  equiv := by
    rw [koszulComplex_zero]
    refine ⟨(HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ) 0
      (ModuleCat.of R R)).toLinearEquiv.trans (Submodule.quotEquivOfEqBot _ ?_).symm⟩
    rw [Set.range_eq_empty, Ideal.span_empty]

/-- 正則列の最後の元は、残りで割った商の上で正則。 -/
lemma isWeaklyRegular_init_and_isSMulRegular_last {n : ℕ} (x : Fin (n + 1) → R)
    (hx : RingTheory.Sequence.IsWeaklyRegular R (List.ofFn x)) :
    RingTheory.Sequence.IsWeaklyRegular R (List.ofFn (Fin.init x)) ∧
      IsSMulRegular (R ⧸ Ideal.span (Set.range (Fin.init x))) (x (Fin.last n)) := by
  rw [List.ofFn_succ', List.concat_eq_append, RingTheory.Sequence.isWeaklyRegular_append_iff,
    RingTheory.Sequence.isWeaklyRegular_singleton_iff] at hx
  change RingTheory.Sequence.IsWeaklyRegular R (List.ofFn (Fin.init x)) ∧
    IsSMulRegular (R ⧸ (Ideal.ofList (List.ofFn (Fin.init x)) • ⊤ : Submodule R R))
      (x (Fin.last n)) at hx
  refine ⟨hx.1, ?_⟩
  have hset : {r : R | r ∈ List.ofFn (Fin.init x)} = Set.range (Fin.init x) := by
    ext; simp [List.mem_ofFn]
  have h : (Ideal.ofList (List.ofFn (Fin.init x)) • ⊤ : Submodule R R) =
      Ideal.span (Set.range (Fin.init x)) := by
    rw [Ideal.smul_eq_mul, Ideal.mul_top, Ideal.ofList, hset]
  rw [h] at hx
  exact hx.2

/-- Koszul 複体は正の次数で零。 -/
lemma koszulComplex_isZero_X_of_pos :
    ∀ {n : ℕ} (x : Fin n → R) (i : ℤ), 0 < i → IsZero ((koszulComplex x).X i)
  | 0, x, i, hi => by
    rw [koszulComplex_zero]
    exact HomologicalComplex.isZero_single_obj_X _ _ _ _ (by omega)
  | n + 1, x, i, hi => by
    rw [koszulComplex_succ, CochainComplex.mappingCone.isZero_X_iff]
    exact ⟨koszulComplex_isZero_X_of_pos (Fin.init x) (i + 1) (by omega),
      koszulComplex_isZero_X_of_pos (Fin.init x) i hi⟩

/-- Koszul 複体は `-n` 次より下で零。 -/
lemma koszulComplex_isZero_X_of_lt :
    ∀ {n : ℕ} (x : Fin n → R) (i : ℤ), i < -(n : ℤ) → IsZero ((koszulComplex x).X i)
  | 0, x, i, hi => by
    rw [koszulComplex_zero]
    exact HomologicalComplex.isZero_single_obj_X _ _ _ _ (by omega)
  | n + 1, x, i, hi => by
    rw [koszulComplex_succ, CochainComplex.mappingCone.isZero_X_iff]
    exact ⟨koszulComplex_isZero_X_of_lt (Fin.init x) (i + 1) (by omega),
      koszulComplex_isZero_X_of_lt (Fin.init x) i (by omega)⟩

/-- Koszul 複体の項は有限自由。 -/
lemma koszulComplex_free_finite_X :
    ∀ {n : ℕ} (x : Fin n → R) (i : ℤ),
      Module.Free R ((koszulComplex x).X i) ∧ Module.Finite R ((koszulComplex x).X i)
  | 0, x, i => by
    rw [koszulComplex_zero]
    by_cases hi : i = 0
    · subst hi
      let e := (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
        (ModuleCat.of R R)).toLinearEquiv
      exact ⟨Module.Free.of_equiv e.symm, Module.Finite.equiv e.symm⟩
    · have h := HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0
        (ModuleCat.of R R) i hi
      exact ⟨isZero_moduleCat_free h, isZero_moduleCat_finite h⟩
  | n + 1, x, i => by
    rw [koszulComplex_succ]
    obtain ⟨h1, h2⟩ := koszulComplex_free_finite_X (Fin.init x) (i + 1)
    obtain ⟨h3, h4⟩ := koszulComplex_free_finite_X (Fin.init x) i
    exact mappingCone_free_finite _ i

/-- Koszul 複体のホモロジーは正の次数で零。 -/
lemma koszulComplex_isZero_homology_of_pos {n : ℕ} (x : Fin n → R) (i : ℤ) (hi : 0 < i) :
    IsZero ((koszulComplex x).homology i) :=
  (HomologicalComplex.exactAt_iff_isZero_homology _ _).mp
    (ShortComplex.exact_of_isZero_X₂ _ (koszulComplex_isZero_X_of_pos x i hi))

/-- 帰納段の `0` 次：`H^1(K') = 0` と `H^0(K') ≃ R/I` から `H^0(Cone(a • 𝟙 K')) ≃ R/(I, a)`。
正則性は要らない。 -/
theorem homologyZeroEquiv_succ {n : ℕ} (x : Fin (n + 1) → R)
    (h1 : IsZero ((koszulComplex (Fin.init x)).homology 1))
    (e : (koszulComplex (Fin.init x)).homology 0 ≃ₗ[R] R ⧸ Ideal.span (Set.range (Fin.init x))) :
    Nonempty ((koszulComplex x).homology 0 ≃ₗ[R] R ⧸ Ideal.span (Set.range x)) := by
  set K := koszulComplex (Fin.init x) with hK
  set a := x (Fin.last n) with ha
  set I : Ideal R := Ideal.span (Set.range (Fin.init x)) with hI
  have hmap : HomologicalComplex.homologyMap (smulId a K) 0 = a • 𝟙 (K.homology 0) := by
    rw [smulId, homologyMap_smul, HomologicalComplex.homologyMap_id]
  change Nonempty ((Cone.cone (smulId a K)).homology 0 ≃ₗ[R] R ⧸ Ideal.span (Set.range x))
  have h2 := Cone.exact₂ (smulId a K) 0
  have h3 := Cone.exact₃ (smulId a K) 0 1 rfl
  have hepi : Epi (HomologicalComplex.homologyMap
      (CochainComplex.mappingCone.inr (smulId a K)) 0) :=
    h3.epi_f (h1.eq_zero_of_tgt _)
  have hsurj : Function.Surjective
      (HomologicalComplex.homologyMap (CochainComplex.mappingCone.inr (smulId a K)) 0).hom :=
    (ModuleCat.epi_iff_surjective _).mp hepi
  have hrk : LinearMap.range (HomologicalComplex.homologyMap (smulId a K) 0).hom =
      LinearMap.ker (HomologicalComplex.homologyMap
        (CochainComplex.mappingCone.inr (smulId a K)) 0).hom :=
    (ShortComplex.moduleCat_exact_iff_range_eq_ker _).mp h2
  rw [hmap] at hrk
  -- `Q = a • (R/I) ⊆ R/I`
  let Q : Submodule R (R ⧸ I) := LinearMap.range (a • LinearMap.id : (R ⧸ I) →ₗ[R] R ⧸ I)
  have hmapQ : (LinearMap.range (a • 𝟙 (K.homology 0)).hom).map (e : K.homology 0 →ₗ[R] R ⧸ I)
      = Q := by
    rw [← LinearMap.range_comp]
    have : (e : K.homology 0 →ₗ[R] R ⧸ I) ∘ₗ (a • 𝟙 (K.homology 0)).hom =
        (a • LinearMap.id : (R ⧸ I) →ₗ[R] R ⧸ I) ∘ₗ (e : K.homology 0 →ₗ[R] R ⧸ I) := by
      ext y
      simp
    rw [this, LinearMap.range_comp_of_range_eq_top _ e.range]
  have hQ : Q = Submodule.span R {Submodule.Quotient.mk a} := by
    ext y
    simp only [Q, LinearMap.mem_range, LinearMap.smul_apply, LinearMap.id_apply,
      Submodule.mem_span_singleton]
    constructor
    · rintro ⟨z, rfl⟩
      obtain ⟨r, rfl⟩ := Submodule.Quotient.mk_surjective I z
      exact ⟨r, by rw [← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_smul, smul_eq_mul,
        smul_eq_mul, mul_comm]⟩
    · rintro ⟨r, rfl⟩
      exact ⟨Submodule.Quotient.mk r, by rw [← Submodule.Quotient.mk_smul,
        ← Submodule.Quotient.mk_smul, smul_eq_mul, smul_eq_mul, mul_comm]⟩
  have hsup : Submodule.map I.mkQ (I ⊔ Submodule.span R {a}) = Q := by
    rw [Submodule.map_sup, Submodule.mkQ_map_self, Submodule.map_span, Set.image_singleton,
      bot_sup_eq, hQ, Submodule.mkQ_apply]
  have hrange : Set.range x = insert a (Set.range (Fin.init x)) := by
    have := Fin.range_snoc (Fin.init x) (x (Fin.last n))
    rwa [Fin.snoc_init_self] at this
  have hspan : I ⊔ Submodule.span R {a} = Ideal.span (Set.range x) := by
    rw [hI, hrange]
    change _ = Submodule.span R _
    rw [Submodule.span_insert, sup_comm]
  have eq₁ : (K.homology 0 ⧸ LinearMap.range (a • 𝟙 (K.homology 0)).hom) ≃ₗ[R]
      (R ⧸ I) ⧸ Q :=
    Submodule.Quotient.equiv _ Q e hmapQ
  have eq₂ : ((R ⧸ I) ⧸ Submodule.map I.mkQ (I ⊔ Submodule.span R {a})) ≃ₗ[R]
      R ⧸ (I ⊔ Submodule.span R {a}) :=
    Submodule.quotientQuotientEquivQuotient I (I ⊔ Submodule.span R {a}) le_sup_left
  exact ⟨(LinearMap.quotKerEquivOfSurjective _ hsurj).symm.trans
    ((Submodule.quotEquivOfEq _ _ hrk.symm).trans (eq₁.trans
      ((Submodule.quotEquivOfEq _ _ hsup.symm).trans
        (eq₂.trans (Submodule.quotEquivOfEq _ _ hspan)))))⟩

/-- `H^0(K(x)) ≃ R/(x)`。正則性は要らない。 -/
theorem koszulComplex_homology_zero_equiv :
    ∀ {n : ℕ} (x : Fin n → R),
      Nonempty ((koszulComplex x).homology 0 ≃ₗ[R] R ⧸ Ideal.span (Set.range x))
  | 0, x => (isKoszulResolution_zero x).equiv
  | _ + 1, x =>
    homologyZeroEquiv_succ x (koszulComplex_isZero_homology_of_pos _ 1 one_pos)
      (koszulComplex_homology_zero_equiv (Fin.init x)).some

/-- 帰納段：`K(x) = Cone(a • 𝟙 K')`、`K'` が `R/I` の分解で `a` が `R/I` 上正則なら、
`K(x)` は `R/(I, a) = R/(x)` の分解。 -/
theorem isKoszulResolution_succ {n : ℕ} (x : Fin (n + 1) → R)
    (ih : IsKoszulResolution (Fin.init x))
    (hreg : IsSMulRegular (R ⧸ Ideal.span (Set.range (Fin.init x))) (x (Fin.last n))) :
    IsKoszulResolution x := by
  set K := koszulComplex (Fin.init x) with hK
  set a := x (Fin.last n) with ha
  set I : Ideal R := Ideal.span (Set.range (Fin.init x)) with hI
  obtain ⟨e⟩ := ih.equiv
  have hmap : ∀ i, HomologicalComplex.homologyMap (smulId a K) i = a • 𝟙 (K.homology i) := by
    intro i
    rw [smulId, homologyMap_smul, HomologicalComplex.homologyMap_id]
  have hinj : Function.Injective (fun y : K.homology 0 ↦ a • y) := by
    intro y z hyz
    apply e.injective
    apply hreg
    simpa only [map_smul] using congrArg e hyz
  have hmono : Mono (a • 𝟙 (K.homology 0)) := by
    rw [ModuleCat.mono_iff_injective]
    intro y z h
    exact hinj (by simpa using h)
  have h10 : (-1 : ℤ) + 1 = 0 := by norm_num
  refine ⟨fun i hi ↦ ?_, homologyZeroEquiv_succ x (ih.isZero 1 one_ne_zero) e⟩
  change IsZero ((Cone.cone (smulId a K)).homology i)
  by_cases hi1 : i = -1
  · subst hi1
    have h3 := Cone.exact₃ (smulId a K) (-1) 0 h10
    have hz : IsZero (K.homology (-1)) := ih.isZero (-1) (by norm_num)
    have hmonoδ : Mono (Cone.δ (smulId a K) (-1) 0 h10) := h3.mono_g (hz.eq_zero_of_src _)
    have hcomp : Cone.δ (smulId a K) (-1) 0 h10 ≫
        HomologicalComplex.homologyMap (smulId a K) 0 = 0 :=
      comp_eq_zero_transport (Cone.S₁ (smulId a K) (-1) 0 h10) _ _ _ _ _
        (Cone.δ_square (smulId a K) (-1) 0 h10) (Cone.e_naturality 0 (smulId a K))
    rw [hmap 0] at hcomp
    have hδ : Cone.δ (smulId a K) (-1) 0 h10 = 0 := zero_of_comp_mono _ hcomp
    rw [IsZero.iff_id_eq_zero, ← cancel_mono (Cone.δ (smulId a K) (-1) 0 h10), Category.id_comp,
      zero_comp, hδ]
  · have h3 := Cone.exact₃ (smulId a K) i (i + 1) rfl
    exact h3.isZero_of_both_isZero (ih.isZero i hi) (ih.isZero (i + 1) (by omega))

/-- **Koszul 複体の完全性**：`x` が弱正則列なら `K(x; R)` は `R/(x)` の分解。 -/
theorem isKoszulResolution_of_isWeaklyRegular {n : ℕ} (x : Fin n → R)
    (hx : RingTheory.Sequence.IsWeaklyRegular R (List.ofFn x)) : IsKoszulResolution x := by
  induction n with
  | zero => exact isKoszulResolution_zero x
  | succ n ih =>
    obtain ⟨hinit, hreg⟩ := isWeaklyRegular_init_and_isSMulRegular_last x hx
    exact isKoszulResolution_succ x (ih _ hinit) hreg

end SerrePositivity
