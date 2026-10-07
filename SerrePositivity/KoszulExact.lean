module

public import SerrePositivity.Koszul
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

前半は一般の複体 `K` と `a : R` に対する `Cone(a • 𝟙 K)` の長完全列の整理。
-/

@[expose] public section

universe u

open CategoryTheory Limits Pretriangulated

namespace SerrePositivity

variable {R : Type u} [CommRing R]

/-- 複体の射のスカラー倍はホモロジーの射のスカラー倍を誘導する。 -/
lemma homologyMap_smul {K L : CochainComplex (ModuleCat.{u} R) ℤ} (f : K ⟶ L) (a : R) (i : ℤ) :
    HomologicalComplex.homologyMap (a • f) i = a • HomologicalComplex.homologyMap f i := by
  have : (HomologicalComplex.shortComplexFunctor _ _ i).map (a • f) =
      a • (HomologicalComplex.shortComplexFunctor _ _ i).map f := by
    ext <;> rfl
  simp only [HomologicalComplex.homologyMap, this, ShortComplex.homologyMap_smul]
  rfl

/-- 短複体 `S` と同型な対象で置き換えた射の合成も零。 -/
lemma comp_eq_zero_transport (S : ShortComplex (ModuleCat.{u} R))
    {X₁ X₂ X₃ : ModuleCat.{u} R} (e₁ : S.X₁ ≅ X₁) (e₂ : S.X₂ ≅ X₂) (e₃ : S.X₃ ≅ X₃)
    (f : X₁ ⟶ X₂) (g : X₂ ⟶ X₃) (h₁ : S.f ≫ e₂.hom = e₁.hom ≫ f)
    (h₂ : S.g ≫ e₃.hom = e₂.hom ≫ g) : f ≫ g = 0 := by
  have hf : f = e₁.inv ≫ S.f ≫ e₂.hom := by rw [h₁, Iso.inv_hom_id_assoc]
  have hg : g = e₂.inv ≫ S.g ≫ e₃.hom := by rw [h₂, Iso.inv_hom_id_assoc]
  rw [hf, hg, Category.assoc, Category.assoc, Iso.hom_inv_id_assoc, S.zero_assoc,
    zero_comp, comp_zero]

/-- 短複体の完全性を、同型な対象で置き換えた短複体に移す。 -/
lemma exact_transport {S : ShortComplex (ModuleCat.{u} R)} (hS : S.Exact)
    {X₁ X₂ X₃ : ModuleCat.{u} R} (e₁ : S.X₁ ≅ X₁) (e₂ : S.X₂ ≅ X₂) (e₃ : S.X₃ ≅ X₃)
    (f : X₁ ⟶ X₂) (g : X₂ ⟶ X₃) (h₁ : S.f ≫ e₂.hom = e₁.hom ≫ f)
    (h₂ : S.g ≫ e₃.hom = e₂.hom ≫ g) :
    (ShortComplex.mk f g (comp_eq_zero_transport S e₁ e₂ e₃ f g h₁ h₂)).Exact :=
  ShortComplex.exact_of_iso (ShortComplex.isoMk e₁ e₂ e₃ h₁.symm h₂.symm) hS

namespace ConeSmul

variable (K : CochainComplex (ModuleCat.{u} R) ℤ) (a : R)

/-- `Cone(a • 𝟙 K)`。 -/
noncomputable abbrev cone : CochainComplex (ModuleCat.{u} R) ℤ :=
  CochainComplex.mappingCone (smulId a K)

/-- 三角 `K → K → Cone → K[1]` は distinguished。 -/
lemma triangleh_distinguished :
    CochainComplex.mappingCone.triangleh (smulId a K) ∈
      distTriang (HomotopyCategory (ModuleCat.{u} R) (ComplexShape.up ℤ)) :=
  HomotopyCategory.mappingCone_triangleh_distinguished _

/-- ホモロジー関手 `H^0`（shift で `H^n` が出る）。 -/
noncomputable abbrev H₀ :
    HomotopyCategory (ModuleCat.{u} R) (ComplexShape.up ℤ) ⥤ ModuleCat.{u} R :=
  HomotopyCategory.homologyFunctor (ModuleCat.{u} R) (ComplexShape.up ℤ) 0

/-- ホモトピー圏のホモロジー関手と複体のホモロジーの同一視。 -/
noncomputable abbrev e (n : ℤ) (L : CochainComplex (ModuleCat.{u} R) ℤ) :
    (HomotopyCategory.homologyFunctor (ModuleCat.{u} R) (ComplexShape.up ℤ) n).obj
      ((HomotopyCategory.quotient _ _).obj L) ≅ L.homology n :=
  (HomotopyCategory.homologyFunctorFactors (ModuleCat.{u} R) (ComplexShape.up ℤ) n).app L

lemma e_naturality (n : ℤ) {L L' : CochainComplex (ModuleCat.{u} R) ℤ} (f : L ⟶ L') :
    (HomotopyCategory.homologyFunctor (ModuleCat.{u} R) (ComplexShape.up ℤ) n).map
        ((HomotopyCategory.quotient _ _).map f) ≫ (e n L').hom =
      (e n L).hom ≫ HomologicalComplex.homologyMap f n :=
  (HomotopyCategory.homologyFunctorFactors (ModuleCat.{u} R) (ComplexShape.up ℤ) n).hom.naturality f

/-- 連結射 `δ : H^n(Cone) → H^{n+1}(K)`。 -/
noncomputable def δ (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) :
    (cone K a).homology n₀ ⟶ K.homology n₁ :=
  (e n₀ (cone K a)).inv ≫
    (H₀ (R := R)).homologySequenceδ (CochainComplex.mappingCone.triangleh (smulId a K)) n₀ n₁ h ≫
    (e n₁ K).hom

lemma δ_square (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) :
    (H₀ (R := R)).homologySequenceδ (CochainComplex.mappingCone.triangleh (smulId a K)) n₀ n₁ h ≫
        (e n₁ K).hom =
      (e n₀ (cone K a)).hom ≫ δ K a n₀ n₁ h := by
  rw [δ, Iso.hom_inv_id_assoc]
  rfl

/-- 三角圏側の短複体 `H^n(K) → H^n(K) → H^n(Cone)`。 -/
noncomputable abbrev S₂ (n : ℤ) : ShortComplex (ModuleCat.{u} R) :=
  ShortComplex.mk _ _ ((H₀ (R := R)).homologySequence_comp _ (triangleh_distinguished K a) n)

/-- 三角圏側の短複体 `H^n(K) → H^n(Cone) → H^{n+1}(K)`。 -/
noncomputable abbrev S₃ (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) : ShortComplex (ModuleCat.{u} R) :=
  ShortComplex.mk _ _ ((H₀ (R := R)).comp_homologySequenceδ _ (triangleh_distinguished K a) n₀ n₁ h)

/-- 三角圏側の短複体 `H^n(Cone) → H^{n+1}(K) → H^{n+1}(K)`。 -/
noncomputable abbrev S₁ (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) : ShortComplex (ModuleCat.{u} R) :=
  ShortComplex.mk _ _ ((H₀ (R := R)).homologySequenceδ_comp _ (triangleh_distinguished K a) n₀ n₁ h)

/-- `H^n(K) → H^n(K) → H^n(Cone)` は完全。 -/
lemma exact₂ (n : ℤ) :
    (ShortComplex.mk (HomologicalComplex.homologyMap (smulId a K) n)
      (HomologicalComplex.homologyMap (CochainComplex.mappingCone.inr (smulId a K)) n)
      (comp_eq_zero_transport (S₂ K a n) (e n K) (e n K) (e n (cone K a)) _ _
        (e_naturality n (smulId a K))
        (e_naturality n (CochainComplex.mappingCone.inr (smulId a K))))).Exact :=
  exact_transport ((H₀ (R := R)).homologySequence_exact₂ _ (triangleh_distinguished K a) n)
    (e n K) (e n K) (e n (cone K a)) _ _ (e_naturality n (smulId a K))
    (e_naturality n (CochainComplex.mappingCone.inr (smulId a K)))

/-- `H^n(K) → H^n(Cone) → H^{n+1}(K)` は完全。 -/
lemma exact₃ (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) :
    (ShortComplex.mk
      (HomologicalComplex.homologyMap (CochainComplex.mappingCone.inr (smulId a K)) n₀)
      (δ K a n₀ n₁ h)
      (comp_eq_zero_transport (S₃ K a n₀ n₁ h) (e n₀ K) (e n₀ (cone K a)) (e n₁ K) _
        (δ K a n₀ n₁ h) (e_naturality n₀ (CochainComplex.mappingCone.inr (smulId a K)))
        (δ_square K a n₀ n₁ h))).Exact :=
  exact_transport ((H₀ (R := R)).homologySequence_exact₃ _ (triangleh_distinguished K a) n₀ n₁ h)
    (e n₀ K) (e n₀ (cone K a)) (e n₁ K) _ (δ K a n₀ n₁ h)
    (e_naturality n₀ (CochainComplex.mappingCone.inr (smulId a K))) (δ_square K a n₀ n₁ h)

/-- `H^n(Cone) → H^{n+1}(K) → H^{n+1}(K)` は完全。 -/
lemma exact₁ (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) :
    (ShortComplex.mk (δ K a n₀ n₁ h) (HomologicalComplex.homologyMap (smulId a K) n₁)
      (comp_eq_zero_transport (S₁ K a n₀ n₁ h) (e n₀ (cone K a)) (e n₁ K) (e n₁ K)
        (δ K a n₀ n₁ h) _ (δ_square K a n₀ n₁ h) (e_naturality n₁ (smulId a K)))).Exact :=
  exact_transport ((H₀ (R := R)).homologySequence_exact₁ _ (triangleh_distinguished K a) n₀ n₁ h)
    (e n₀ (cone K a)) (e n₁ K) (e n₁ K) (δ K a n₀ n₁ h) _ (δ_square K a n₀ n₁ h)
    (e_naturality n₁ (smulId a K))

end ConeSmul

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
  change Nonempty ((ConeSmul.cone K a).homology 0 ≃ₗ[R] R ⧸ Ideal.span (Set.range x))
  have h2 := ConeSmul.exact₂ K a 0
  have h3 := ConeSmul.exact₃ K a 0 1 rfl
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
  change IsZero ((ConeSmul.cone K a).homology i)
  by_cases hi1 : i = -1
  · subst hi1
    have h3 := ConeSmul.exact₃ K a (-1) 0 h10
    have hz : IsZero (K.homology (-1)) := ih.isZero (-1) (by norm_num)
    have hmonoδ : Mono (ConeSmul.δ K a (-1) 0 h10) := h3.mono_g (hz.eq_zero_of_src _)
    have hcomp : ConeSmul.δ K a (-1) 0 h10 ≫ HomologicalComplex.homologyMap (smulId a K) 0 = 0 :=
      comp_eq_zero_transport (ConeSmul.S₁ K a (-1) 0 h10) _ _ _ _ _
        (ConeSmul.δ_square K a (-1) 0 h10) (ConeSmul.e_naturality 0 (smulId a K))
    rw [hmap 0] at hcomp
    have hδ : ConeSmul.δ K a (-1) 0 h10 = 0 := zero_of_comp_mono _ hcomp
    rw [IsZero.iff_id_eq_zero, ← cancel_mono (ConeSmul.δ K a (-1) 0 h10), Category.id_comp,
      zero_comp, hδ]
  · have h3 := ConeSmul.exact₃ K a i (i + 1) rfl
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
