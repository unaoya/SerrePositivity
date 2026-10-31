module

public import SerrePositivity.LengthAlgebra.Flat
public import SerrePositivity.LengthAlgebra.Normalized
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.RingTheory.Ideal.Quotient.Noetherian
public import SerrePositivity.PerfectComplex.Free.Euler
public import SerrePositivity.HomologicalAlgebra.Complex.Truncation
public import SerrePositivity.LengthAlgebra.Perfect
public import SerrePositivity.PerfectComplex.Perfect.HomotopyCategory

/-! # パラメータ商の Tor と正規化長さ

## 概要

R 代数 C、R 正則列 x、B = R/(x)、U = C/(x)C について、Koszul ホモロジーの評価から B 加群の Tor と U の正規化長さを比べ（論文 Lemma 5.3 の前半）、長さ d 以下の有限自由分解を持つ x で消える加群について Tor の正規化長さが消えること（後半）を示す。

## 方針

Koszul 複体による Tor の計算と、正規化長さの加法性・Koszul の消滅を使う。

## 規約

Koszul ホモロジーの評価は明示的な仮定として受け取る。

## 使われ方

Paper の §5（Lemma 5.3）。
-/

@[expose] public noncomputable section

universe u

section ParameterQuotientTorPart

open CategoryTheory Limits
open scoped ENNReal

namespace SerrePositivity

/-! ## 一般論：次元シフト -/

section shift

variable {A C' : Type u} [CommRing A] [CommRing C'] (φ' : A →+* C') {J' : Ideal C'}
  (μ : NormalizedLength C' J')

/-- **次元シフト**：短完全列 `0 → V₁ → V₂ → V₃ → 0` で `λ(Tor_i(V₂)) = 0`（`i > 0`）なら
`λ(Tor_{i+2}(V₃)) = λ(Tor_{i+1}(V₁))` と
`λ(Tor_1(V₃)) + λ(Tor_0(V₂)) = λ(Tor_0(V₁)) + λ(Tor_0(V₃))`。長完全列の各項を核と像に分ける。 -/
theorem len_torAlg_shift {V₁ V₂ V₃ : Type u} [AddCommGroup V₁] [Module A V₁]
    [AddCommGroup V₂] [Module A V₂] [AddCommGroup V₃] [Module A V₃]
    (f : V₁ →ₗ[A] V₂) (g : V₂ →ₗ[A] V₃) (hf : Function.Injective f) (hg : Function.Surjective g)
    (hfg : Function.Exact f g)
    (t₁ : ∀ i, IsPowTorsion J' (TorAlg φ' i V₁)) (t₂ : ∀ i, IsPowTorsion J' (TorAlg φ' i V₂))
    (t₃ : ∀ i, IsPowTorsion J' (TorAlg φ' i V₃))
    (h₂ : ∀ i, 0 < i → μ.len (TorAlg φ' i V₂) = 0) :
    (∀ i, μ.len (TorAlg φ' (i + 2) V₃) = μ.len (TorAlg φ' (i + 1) V₁)) ∧
      μ.len (TorAlg φ' 1 V₃) + μ.len (TorAlg φ' 0 V₂) =
        μ.len (TorAlg φ' 0 V₁) + μ.len (TorAlg φ' 0 V₃) := by
  obtain ⟨α, β, δ, e₁, e₂, e₃, hβ⟩ := torAlg_longExact φ' f g hf hg hfg
  -- `λ(Tor_{j+1}(V₃)) = λ(ker α_j)`
  have key : ∀ j, μ.len (TorAlg φ' (j + 1) V₃) = μ.len (LinearMap.ker (α j)) := by
    intro j
    rw [μ.len_eq_add_ker_range (δ j) (t₃ (j + 1)), LinearMap.exact_iff.mp (e₂ j),
      ← LinearMap.exact_iff.mp (e₃ j),
      μ.len_range_eq_zero (β (j + 1)) (t₂ (j + 1)) (h₂ (j + 1) (Nat.succ_pos j)), zero_add]
  refine ⟨fun i ↦ ?_, ?_⟩
  · rw [key (i + 1), μ.len_eq_add_ker_range (α (i + 1)) (t₁ (i + 1))]
    have : μ.len (LinearMap.range (α (i + 1))) = 0 :=
      le_antisymm ((μ.len_submodule_le (t₂ (i + 1)) _).trans
        (h₂ (i + 1) (Nat.succ_pos i)).le) zero_le
    rw [this, add_zero]
  · rw [key 0, μ.len_eq_add_ker_range (α 0) (t₁ 0), μ.len_eq_add_ker_range (β 0) (t₂ 0),
      LinearMap.exact_iff.mp (e₁ 0), LinearMap.range_eq_top.mpr hβ,
      μ.len_congr _ _ (Submodule.topEquiv (R := C') (M := TorAlg φ' 0 V₃)), add_assoc]

end shift

/-! ## 冪ねじれ -/

/-- `J^a ⊆ I` なら、`I` で消える加群は `J` 冪ねじれ。 -/
lemma isPowTorsion_of_le {C : Type u} [CommRing C] {J I : Ideal C} {a : ℕ} (hJ : J ^ a ≤ I)
    (M : Type u) [AddCommGroup M] [Module C M] (hM : ∀ c ∈ I, ∀ m : M, c • m = 0) :
    IsPowTorsion J M := by
  refine ⟨a, fun m c ↦ ?_⟩
  exact hM c (hJ c.2) m

namespace ParamQuot

variable {R C : Type u} [CommRing R] [CommRing C] (φ : R →+* C) {h : ℕ} (x : Fin h → R)

/-- `B = R/(x)`。 -/
abbrev B : Type u := R ⧸ Ideal.span (Set.range x)

/-- `(x)C`。 -/
abbrev IC : Ideal C := (Ideal.span (Set.range x)).map φ

/-- `U = C/(x)C`。 -/
abbrev U : Type u := C ⧸ IC φ x

/-- `ψ : B → U`。 -/
noncomputable abbrev ψ : B x →+* U φ x :=
  Ideal.quotientMap (IC φ x) φ Ideal.le_comap_map

/-- `(x)C = (φ x)`。 -/
lemma IC_eq : IC φ x = Ideal.span (Set.range (φ ∘ x)) := by
  rw [IC, Ideal.map_span, ← Set.range_comp]

/-- `B` 加群 `L` の `Tor_i^R(C, L)` は `(x)C` で消える。 -/
lemma torAlg_IC_smul (i : ℕ) (L : Type u) [AddCommGroup L] [Module R L] [Module (B x) L]
    [IsScalarTower R (B x) L] : ∀ c ∈ IC φ x, ∀ t : TorAlg φ i L, c • t = 0 := by
  have hle : IC φ x ≤ Module.annihilator C (TorAlg φ i L) := by
    rw [IC_eq, Ideal.span_le]
    rintro _ ⟨j, rfl⟩
    rw [SetLike.mem_coe, Module.mem_annihilator]
    refine torAlg_smul_eq_zero φ i L (x j) fun v ↦ ?_
    rw [← algebraMap_smul (B x) (x j) v, Ideal.Quotient.algebraMap_eq,
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_range_self j)), zero_smul]
  exact fun c hc t ↦ Module.mem_annihilator.mp (hle hc) t

/-! ## 0 次：`C ⊗_R L ≃ U ⊗_B L` -/

section tensor

open scoped ChangeOfRings

variable (L : Type u) [AddCommGroup L] [Module R L] [Module (B x) L] [IsScalarTower R (B x) L]

/-- `Tor_0^R(C, L) = C ⊗_R L`（係数拡大の対象）。 -/
abbrev T1 : Type u := (ModuleCat.extendScalars φ).obj (ModuleCat.of R L)
/-- `Tor_0^B(U, L) = U ⊗_B L`。 -/
abbrev T2 : Type u := (ModuleCat.extendScalars (ψ φ x)).obj (ModuleCat.of (B x) L)

/-- `C ⊗_R L` で `(φ r · c) ⊗ l = c ⊗ r l`。 -/
lemma T1_tmul_smul (r : R) (c : C) (l : L) :
    ((φ r * c) ⊗ₜ[R, φ] l : T1 φ L) = (c ⊗ₜ[R, φ] (r • l) : T1 φ L) := by
  let _ : Module R C := Module.compHom C φ
  exact TensorProduct.smul_tmul (R := R) (M := C) (N := L) r c l

/-- `C ⊗_R L` で `(φ x_j · c) ⊗ l = 0`（`x_j L = 0`）。 -/
lemma T1_tmul_eq_zero (j : Fin h) (c : C) (l : L) : ((φ (x j) * c) ⊗ₜ[R, φ] l : T1 φ L) = 0 := by
  rw [T1_tmul_smul, ← algebraMap_smul (B x) (x j) l, Ideal.Quotient.algebraMap_eq,
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_range_self j)), zero_smul]
  exact TensorProduct.tmul_zero _ _

/-- `l ↦ 1 ⊗ l`。 -/
noncomputable def oneTmul : L →+ T1 φ L where
  toFun l := ((1 : C) ⊗ₜ[R, φ] l : T1 φ L)
  map_zero' := TensorProduct.tmul_zero _ _
  map_add' _ _ := TensorProduct.tmul_add _ _ _

lemma smul_oneTmul (c : C) (l : L) :
    c • oneTmul φ L l = (c ⊗ₜ[R, φ] l : (ModuleCat.extendScalars φ).obj (ModuleCat.of R L)) := by
  have := ModuleCat.ExtendScalars.smul_tmul φ (M := ModuleCat.of R L) c 1 l
  rw [mul_one] at this
  exact this

/-- `[c] ↦ (l ↦ c ⊗ l)`。 -/
noncomputable def bwdU : U φ x →ₗ[C] (L →+ T1 φ L) :=
  (IC φ x).liftQ (LinearMap.toSpanSingleton C _ (oneTmul φ L)) (by
    rw [IC_eq, Ideal.span_le]
    rintro _ ⟨j, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.toSpanSingleton_apply]
    ext l
    rw [AddMonoidHom.smul_apply, AddMonoidHom.zero_apply, smul_oneTmul]
    have := T1_tmul_eq_zero φ x L j 1 l
    rwa [mul_one] at this)

lemma bwdU_mk (c : C) (l : L) :
    bwdU φ x L (Ideal.Quotient.mk (IC φ x) c) l = (c ⊗ₜ[R, φ] l : T1 φ L) := by
  change (c • oneTmul φ L) l = _
  rw [AddMonoidHom.smul_apply, smul_oneTmul]

/-- `C ⊗_R L → U ⊗_B L`、`c ⊗ l ↦ [c] ⊗ l`。 -/
noncomputable def fwd : T1 φ L →+ T2 φ x L :=
  TensorProduct.liftAddHom
    { toFun := fun c ↦
        { toFun := fun l ↦ (Ideal.Quotient.mk (IC φ x) (show C from c)) ⊗ₜ[B x, ψ φ x] l
          map_zero' := TensorProduct.tmul_zero _ _
          map_add' := fun _ _ ↦ TensorProduct.tmul_add _ _ _ }
      map_zero' := by
        ext l
        let _ := Module.compHom (U φ x) (ψ φ x)
        change (Ideal.Quotient.mk (IC φ x) (0 : C)) ⊗ₜ[B x] l = 0
        rw [map_zero]
        exact TensorProduct.zero_tmul _ _
      map_add' := fun c d ↦ by
        ext l
        let _ := Module.compHom (U φ x) (ψ φ x)
        change (Ideal.Quotient.mk (IC φ x) ((show C from c) + (show C from d))) ⊗ₜ[B x] l =
          (Ideal.Quotient.mk (IC φ x) (show C from c)) ⊗ₜ[B x] l +
            (Ideal.Quotient.mk (IC φ x) (show C from d)) ⊗ₜ[B x] l
        rw [map_add]
        exact TensorProduct.add_tmul _ _ _ }
    (by
      intro r c l
      let _ := Module.compHom (U φ x) (ψ φ x)
      change (Ideal.Quotient.mk (IC φ x) (φ r * show C from c)) ⊗ₜ[B x] l =
        (Ideal.Quotient.mk (IC φ x) (show C from c)) ⊗ₜ[B x] (r • l)
      rw [← algebraMap_smul (B x) r l, ← TensorProduct.smul_tmul]
      rfl)

/-- `U ⊗_B L → C ⊗_R L`、`[c] ⊗ l ↦ c ⊗ l`。 -/
noncomputable def bwd : T2 φ x L →+ T1 φ L :=
  TensorProduct.liftAddHom (bwdU φ x L).toAddMonoidHom (by
    intro b u l
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective b
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective u
    change bwdU φ x L (Ideal.Quotient.mk (IC φ x) (φ r * c)) l =
      bwdU φ x L (Ideal.Quotient.mk (IC φ x) c) ((Ideal.Quotient.mk _ r : B x) • l)
    rw [show (Ideal.Quotient.mk _ r : B x) • l = r • l from algebraMap_smul (B x) r l,
      bwdU_mk, bwdU_mk]
    exact T1_tmul_smul φ L r c l)

lemma bwd_tmul (c : C) (l : L) :
    bwd φ x L ((Ideal.Quotient.mk (IC φ x) c) ⊗ₜ[B x, ψ φ x] l) = (c ⊗ₜ[R, φ] l : T1 φ L) :=
  bwdU_mk φ x L c l

lemma bwd_fwd (t : T1 φ L) : bwd φ x L (fwd φ x L t) = t := by
  induction t using TensorProduct.inductionOn with
  | tmul c l => exact bwd_tmul φ x L c l
  | add s t hs ht =>
    exact (congrArg (bwd φ x L) (map_add (fwd φ x L) s t)).trans
      ((map_add (bwd φ x L) _ _).trans (congrArg₂ (· + ·) hs ht))

lemma fwd_bwd (t : T2 φ x L) : fwd φ x L (bwd φ x L t) = t := by
  induction t using TensorProduct.inductionOn with
  | tmul u l =>
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective (show C ⧸ IC φ x from u)
    exact congrArg (fwd φ x L) (bwd_tmul φ x L c l)
  | add s t hs ht =>
    exact (congrArg (fwd φ x L) (map_add (bwd φ x L) s t)).trans
      ((map_add (fwd φ x L) _ _).trans (congrArg₂ (· + ·) hs ht))

lemma fwd_smul (c : C) (t : T1 φ L) :
    fwd φ x L (c • t) = (Ideal.Quotient.mk (IC φ x) c) • fwd φ x L t := by
  induction t using TensorProduct.inductionOn with
  | tmul d l =>
    have h1 := ModuleCat.ExtendScalars.smul_tmul φ (M := ModuleCat.of R L) c (show C from d) l
    have h2 := ModuleCat.ExtendScalars.smul_tmul (ψ φ x) (M := ModuleCat.of (B x) L)
      (Ideal.Quotient.mk (IC φ x) c) (Ideal.Quotient.mk (IC φ x) (show C from d)) l
    exact (congrArg (fwd φ x L) h1).trans h2.symm
  | add s t hs ht =>
    have e1 := smul_add (A := T1 φ L) c s t
    have e2 := smul_add (A := T2 φ x L) (Ideal.Quotient.mk (IC φ x) c) (fwd φ x L s) (fwd φ x L t)
    exact (congrArg (fwd φ x L) e1).trans ((map_add (fwd φ x L) _ _).trans
      ((congrArg₂ (· + ·) hs ht).trans (e2.symm.trans (congrArg _ (map_add (fwd φ x L) s t).symm))))

/-- **0 次の比較**：`C ⊗_R L ≃ U ⊗_B L`（`C` 線形、右辺は `C → U` で `C` 加群とみる）。 -/
noncomputable def tensorEquiv :
    letI := Module.compHom (T2 φ x L) (Ideal.Quotient.mk (IC φ x))
    T1 φ L ≃ₗ[C] T2 φ x L :=
  letI := Module.compHom (T2 φ x L) (Ideal.Quotient.mk (IC φ x))
  { toFun := fwd φ x L
    invFun := bwd φ x L
    map_add' := map_add _
    map_smul' := fwd_smul φ x L
    left_inv := bwd_fwd φ x L
    right_inv := fwd_bwd φ x L }

/-- **0 次**：`λ_U(Tor_0^B(U, L)) = λ(Tor_0^R(C, L))`。 -/
theorem len_torAlg_zero {J : Ideal C} (lam : NormalizedLength C J) :
    (lam.comap (Ideal.Quotient.mk (IC φ x)) (J.map (Ideal.Quotient.mk (IC φ x))) le_rfl).len
      (TorAlg (ψ φ x) 0 L) = lam.len (TorAlg φ 0 L) := by
  rw [NormalizedLength.comap_len]
  let _ := Module.compHom (TorAlg (ψ φ x) 0 L) (Ideal.Quotient.mk (IC φ x))
  let _ := Module.compHom (T2 φ x L) (Ideal.Quotient.mk (IC φ x))
  let e0R : TorAlg φ 0 L ≃ₗ[C] T1 φ L :=
    ((ModuleCat.extendScalars φ).leftDerivedZeroIsoSelf.app (ModuleCat.of R L)).toLinearEquiv
  let e0B : TorAlg (ψ φ x) 0 L ≃ₗ[U φ x] T2 φ x L :=
    ((ModuleCat.extendScalars (ψ φ x)).leftDerivedZeroIsoSelf.app
      (ModuleCat.of (B x) L)).toLinearEquiv
  let e0B' : TorAlg (ψ φ x) 0 L ≃ₗ[C] T2 φ x L :=
    { e0B with map_smul' := fun c t ↦ e0B.map_smul (Ideal.Quotient.mk (IC φ x) c) t }
  exact (lam.len_congr _ _ (e0R.trans ((tensorEquiv φ x L).trans e0B'.symm))).symm

end tensor

variable {φ x} {J : Ideal C} {a : ℕ} (hJ : J ^ a ≤ IC φ x)

include hJ in
lemma isPowTorsion_torAlg (i : ℕ) (L : Type u) [AddCommGroup L] [Module R L] [Module (B x) L]
    [IsScalarTower R (B x) L] : IsPowTorsion J (TorAlg φ i L) :=
  isPowTorsion_of_le hJ _ (torAlg_IC_smul φ x i L)

include hJ in
/-- `U` 加群はすべて `J U` 冪ねじれ（`(J U)^a ⊆ (x)C U = 0`）。 -/
lemma isPowTorsion_U (M : Type u) [AddCommGroup M] [Module (U φ x) M] :
    IsPowTorsion (J.map (Ideal.Quotient.mk (IC φ x))) M := by
  refine ⟨a, fun m c ↦ ?_⟩
  have : (c : U φ x) = 0 := by
    have hc : (c : U φ x) ∈ (J ^ a).map (Ideal.Quotient.mk (IC φ x)) := by
      rw [Ideal.map_pow]; exact c.2
    have := Ideal.map_mono (f := Ideal.Quotient.mk (IC φ x)) hJ hc
    rwa [Ideal.map_quotient_self, Ideal.mem_bot] at this
  rw [this, zero_smul]

variable (lam : NormalizedLength C J)

variable (φ x) in
/-- `B` 側の正規化長さ `λ_U`：`U` 加群を `C → U` で `C` 加群とみて `λ` で測る。 -/
noncomputable abbrev lamU : NormalizedLength (U φ x) (J.map (Ideal.Quotient.mk (IC φ x))) :=
  lam.comap (Ideal.Quotient.mk (IC φ x)) _ le_rfl

/-! ## 自由加群での値 -/

variable (hreg : RingTheory.Sequence.IsWeaklyRegular R (List.ofFn x))
  (hzero : ∀ q : ℕ, 0 < q → lam.len (koszulHomologySelf (φ ∘ x) q) = 0)
  (hUfin : lam.len (U φ x) ≠ ⊤)

include hreg hzero hUfin in
/-- `Tor_i^R(C, B) ≅ H_i(x; C)`：`λ = 0`（`i > 0`）、`0` 次は `λ(U) < ∞`。 -/
lemma len_torAlg_B (i : ℕ) :
    (0 < i → lam.len (TorAlg φ i (B x)) = 0) ∧ lam.len (TorAlg φ i (B x)) ≠ ⊤ := by
  have hK := isKoszulResolution_of_isWeaklyRegular x hreg
  have hk : lam.len (TorAlg φ i (B x)) = lam.len (koszulHomologySelf (φ ∘ x) i) :=
    lam.len_congr _ _ (torAlgKoszulEquiv φ x hK i)
  rcases i with _ | i
  · refine ⟨fun h ↦ absurd h (lt_irrefl 0), ?_⟩
    have h0 : lam.len (koszulHomologySelf (φ ∘ x) 0) =
        lam.len (C ⧸ Ideal.span (Set.range (φ ∘ x))) :=
      lam.len_congr _ _ (koszulComplex_homology_zero_equiv (φ ∘ x)).some
    rw [hk, h0, ← lam.len_congr _ _ (Submodule.quotEquivOfEq _ _ (IC_eq φ x))]
    exact hUfin
  · rw [hk, hzero (i + 1) (Nat.succ_pos i)]
    exact ⟨fun _ ↦ rfl, ENNReal.zero_ne_top⟩

include hJ hreg hzero hUfin in
/-- `Tor_i^R(C, B^r)`：`λ = 0`（`i > 0`）、有限。`r` についての帰納法。 -/
lemma len_torAlg_free (r i : ℕ) :
    (0 < i → lam.len (TorAlg φ i (Fin r → B x)) = 0) ∧
      lam.len (TorAlg φ i (Fin r → B x)) ≠ ⊤ := by
  induction r generalizing i with
  | zero =>
    have := torAlg_subsingleton φ i (Fin 0 → B x)
    rw [lam.len_eq_zero_of_subsingleton]
    exact ⟨fun _ ↦ rfl, ENNReal.zero_ne_top⟩
  | succ r ih =>
    let f : B x →ₗ[R] (Fin (r + 1) → B x) := LinearMap.single R (fun _ ↦ B x) 0
    let g : (Fin (r + 1) → B x) →ₗ[R] (Fin r → B x) := LinearMap.funLeft R (B x) Fin.succ
    have hf : Function.Injective f := fun b c hbc ↦ by simpa [f] using congrFun hbc 0
    have hg : Function.Surjective g :=
      LinearMap.funLeft_surjective_of_injective _ _ _ (Fin.succ_injective r)
    have hfg : Function.Exact f g := by
      intro v
      constructor
      · intro hv
        refine ⟨v 0, funext fun k ↦ ?_⟩
        refine Fin.cases ?_ (fun k ↦ ?_) k
        · simp [f]
        · have hk := congrFun hv k
          simp only [g, LinearMap.funLeft_apply, Pi.zero_apply] at hk
          simp [f, Fin.succ_ne_zero, hk]
      · rintro ⟨b, rfl⟩
        funext k
        simp [f, g, LinearMap.funLeft_apply, Fin.succ_ne_zero]
    obtain ⟨α, β, -, e₁, -, -, -⟩ := torAlg_longExact φ f g hf hg hfg
    have hle := lam.len_le_add_of_exact (α i) (β i) (e₁ i) (isPowTorsion_torAlg hJ i _)
      (isPowTorsion_torAlg hJ i _) (isPowTorsion_torAlg hJ i _)
    obtain ⟨hB0, hBf⟩ := len_torAlg_B lam hreg hzero hUfin i
    obtain ⟨hr0, hrf⟩ := ih i
    refine ⟨fun hi ↦ ?_, ne_top_of_le_ne_top (WithTop.add_ne_top.mpr ⟨hBf, hrf⟩) hle⟩
    rw [hB0 hi, hr0 hi, add_zero] at hle
    exact le_antisymm hle zero_le

omit hJ in
/-- `Tor_{i+1}^B(U, B^r) = 0`（射影加群）。 -/
lemma len_torAlg_free_B (r i : ℕ) :
    (lamU φ x lam).len (TorAlg (ψ φ x) (i + 1) (Fin r → B x)) = 0 := by
  have : Subsingleton (TorAlg (ψ φ x) (i + 1) (Fin r → B x)) :=
    ModuleCat.subsingleton_of_isZero
      ((ModuleCat.extendScalars (ψ φ x)).isZero_leftDerived_obj_projective_succ i
        (ModuleCat.of (B x) (Fin r → B x)))
  exact (lamU φ x lam).len_eq_zero_of_subsingleton _

/-! ## 主定理 -/

variable (φ x) in
/-- 主張：すべての有限生成 `B` 加群 `L` で `λ_U(Tor_i^B(U, L)) = λ(Tor_i^R(C, L)) ≠ ⊤`。 -/
def TorClaim (i : ℕ) : Prop :=
  ∀ (L : Type u) [AddCommGroup L] [Module R L] [Module (B x) L] [IsScalarTower R (B x) L]
    [Module.Finite (B x) L],
    (lamU φ x lam).len (TorAlg (ψ φ x) i L) = lam.len (TorAlg φ i L) ∧
      lam.len (TorAlg φ i L) ≠ ⊤

/-- 有限生成 `B` 加群の表示 `0 → L' → B^r → L → 0` を作る。 -/
lemma exists_presentation (L : Type u) [AddCommGroup L] [Module (B x) L] [Module.Finite (B x) L] :
    ∃ (r : ℕ) (g : (Fin r → B x) →ₗ[B x] L), Function.Surjective g :=
  Module.Finite.exists_fin' (B x) L

variable [IsNoetherianRing R]

omit [IsNoetherianRing R] in
include hJ hreg hzero hUfin in
/-- 0 次。 -/
lemma torClaim_zero : TorClaim φ x lam 0 := by
  intro L _ _ _ _ _
  refine ⟨len_torAlg_zero φ x L lam, ?_⟩
  obtain ⟨r, g, hg⟩ := exists_presentation (x := x) L
  obtain ⟨α, β, -, -, -, -, hβ⟩ := torAlg_longExact φ ((LinearMap.ker g).subtype.restrictScalars R)
    (g.restrictScalars R) (LinearMap.ker g).injective_subtype hg
    (LinearMap.exact_subtype_ker_map g)
  exact ne_top_of_le_ne_top (len_torAlg_free hJ lam hreg hzero hUfin r 0).2
    (lam.len_le_of_surjective (β 0) hβ (isPowTorsion_torAlg hJ 0 _))

include hJ hreg hzero hUfin in
/-- **Lemma 5.3 の前半**：有限生成 `B` 加群 `L` について `λ(Tor_i^B(U, L)) = λ(Tor_i^R(C, L))`、
どちらも有限。 -/
theorem torClaim : ∀ i, TorClaim φ x lam i
  | 0 => torClaim_zero hJ lam hreg hzero hUfin
  | 1 => by
    intro L _ _ _ _ _
    obtain ⟨r, g, hg⟩ := exists_presentation (x := x) L
    have : IsNoetherian (B x) (LinearMap.ker g) := isNoetherian_submodule' _
    have : Module.Finite (B x) (LinearMap.ker g) := Module.IsNoetherian.finite _ _
    have h0 := torClaim_zero hJ lam hreg hzero hUfin
    obtain ⟨-, shR⟩ := len_torAlg_shift φ lam ((LinearMap.ker g).subtype.restrictScalars R)
      (g.restrictScalars R) (LinearMap.ker g).injective_subtype hg
      (LinearMap.exact_subtype_ker_map g) (fun i ↦ isPowTorsion_torAlg hJ i _)
      (fun i ↦ isPowTorsion_torAlg hJ i _) (fun i ↦ isPowTorsion_torAlg hJ i _)
      (fun i hi ↦ (len_torAlg_free hJ lam hreg hzero hUfin r i).1 hi)
    obtain ⟨-, shB⟩ := len_torAlg_shift (ψ φ x) (lamU φ x lam) (LinearMap.ker g).subtype g
      (LinearMap.ker g).injective_subtype hg (LinearMap.exact_subtype_ker_map g)
      (fun i ↦ isPowTorsion_U hJ _) (fun i ↦ isPowTorsion_U hJ _) (fun i ↦ isPowTorsion_U hJ _)
      (fun i hi ↦ by
        obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_lt hi
        rw [zero_add]
        exact len_torAlg_free_B (φ := φ) (x := x) lam r j)
    obtain ⟨eF, fF⟩ := h0 (Fin r → B x)
    obtain ⟨eK, fK⟩ := h0 (LinearMap.ker g)
    obtain ⟨eL, fL⟩ := h0 L
    rw [eF, eK, eL, ← shR] at shB
    refine ⟨(ENNReal.add_left_inj fF).mp shB, ?_⟩
    exact ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨fK, fL⟩) (le_self_add.trans_eq shR)
  | i + 2 => by
    intro L _ _ _ _ _
    obtain ⟨r, g, hg⟩ := exists_presentation (x := x) L
    have : IsNoetherian (B x) (LinearMap.ker g) := isNoetherian_submodule' _
    have : Module.Finite (B x) (LinearMap.ker g) := Module.IsNoetherian.finite _ _
    obtain ⟨shR, -⟩ := len_torAlg_shift φ lam ((LinearMap.ker g).subtype.restrictScalars R)
      (g.restrictScalars R) (LinearMap.ker g).injective_subtype hg
      (LinearMap.exact_subtype_ker_map g) (fun i ↦ isPowTorsion_torAlg hJ i _)
      (fun i ↦ isPowTorsion_torAlg hJ i _) (fun i ↦ isPowTorsion_torAlg hJ i _)
      (fun i hi ↦ (len_torAlg_free hJ lam hreg hzero hUfin r i).1 hi)
    obtain ⟨shB, -⟩ := len_torAlg_shift (ψ φ x) (lamU φ x lam) (LinearMap.ker g).subtype g
      (LinearMap.ker g).injective_subtype hg (LinearMap.exact_subtype_ker_map g)
      (fun i ↦ isPowTorsion_U hJ _) (fun i ↦ isPowTorsion_U hJ _) (fun i ↦ isPowTorsion_U hJ _)
      (fun i hi ↦ by
        obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_lt hi
        rw [zero_add]
        exact len_torAlg_free_B (φ := φ) (x := x) lam r j)
    obtain ⟨e, f⟩ := torClaim (i + 1) (LinearMap.ker g)
    rw [shR i, shB i]
    exact ⟨e, f⟩

end ParamQuot

end SerrePositivity

end ParameterQuotientTorPart

section ParameterQuotientTorBoundPart

open CategoryTheory Limits
open scoped ENNReal

namespace SerrePositivity

namespace TorBound

variable {C : Type u} [CommRing C]

/-- `a` がホモトピー圏で `X` 上の零写像として作用すること（`a • 𝟙 X` が零ホモトピック）。 -/
def Kills (a : C) (X : CochainComplex (ModuleCat.{u} C) ℤ) : Prop :=
  a • 𝟙 ((homotopyQuot C).obj X) = 0

end TorBound

/-! ## Lemma 5.3 の後半 -/

namespace ParamQuot

open TorBound

variable {R C : Type u} [CommRing R] [CommRing C] (φ : R →+* C) {h : ℕ} (x : Fin h → R)
  {J : Ideal C} (lam : NormalizedLength C J)

/-- `L` を消す `r` の冪は、`L` の射影分解の上で零ホモトピック。 -/
lemma exists_pow_kills_resolution (L : Type u) [AddCommGroup L] [Module R L]
    {d : ℕ} (P : CochainComplex (ModuleCat.{u} R) ℤ) (hP : IsResolutionOf P (ModuleCat.of R L))
    (hlen : ∀ i, i < -(d : ℤ) → IsZero (P.X i)) (r : R) (hr : ∀ l : L, r • l = 0) :
    ∃ w : ℕ, Nonempty (Homotopy (r ^ w • 𝟙 P) 0) := by
  refine exists_pow_nullHomotopy_of_homology_annihilated P r hP.projective
    ⟨-(d : ℤ), 0, fun i hi ↦ hi.elim (hlen i) (hP.isZero_X i)⟩ fun i ↦ ?_
  by_cases hi : i = 0
  · subst hi
    rw [← cancel_mono hP.homologyZeroIso.hom, zero_comp, Linear.smul_comp, Category.id_comp,
      ← Category.comp_id hP.homologyZeroIso.hom, ← Linear.comp_smul]
    convert comp_zero
    ext l
    exact hr l
  · exact (hP.isZero_homology i hi).eq_of_src _ _

/-- **Lemma 5.3 の後半**：`x_j L = 0`、`L` の長さ `d` 以下の有限自由分解、`J` は有限生成で
`J ⊆ √((x)C)`、Koszul ホモロジーの評価 `λ(H_q(x^v; C)) = 0`（`q, v > 0`）なら、
`i + h > d` で `λ(Tor_i^R(C, L)) = 0`。 -/
theorem len_torAlg_eq_zero (hfg : J.FG) (hJ : J ≤ (Ideal.span (Set.range (φ ∘ x))).radical)
    (hzero : ∀ v : ℕ, 0 < v → ∀ q : ℕ, 0 < q →
      lam.len (koszulHomologySelf (fun j ↦ φ (x j ^ v)) q) = 0)
    (L : Type u) [AddCommGroup L] [Module R L] (hL : ∀ j (l : L), x j • l = 0)
    {d : ℕ} (P : CochainComplex (ModuleCat.{u} R) ℤ) (hP : IsResolutionOf P (ModuleCat.of R L))
    (hfree : ∀ i, Module.Free R (P.X i)) (hfin : ∀ i, Module.Finite R (P.X i))
    (hlen : ∀ i, i < -(d : ℤ) → IsZero (P.X i)) (i : ℕ) (hi : d < i + h) :
    lam.len (TorAlg φ i L) = 0 := by
  let PC := baseChange φ P
  -- 各 `x_j` の冪が `P` 上で零ホモトピック。共通の冪 `w ≥ 1` をとる
  choose ws hws using fun j ↦ exists_pow_kills_resolution L P hP hlen (x j) (hL j)
  let w := Finset.univ.sup ws + 1
  have hw : 0 < w := Nat.succ_pos _
  have hkill : ∀ j, Kills (φ (x j) ^ w) PC := by
    intro j
    obtain ⟨H⟩ := hws j
    have hP' : (x j) ^ w • 𝟙 ((homotopyQuot R).obj P) = 0 :=
      pow_smul_id_eq_zero_of_le ((nonempty_homotopy_smul_id_zero_iff _ P).mp ⟨H⟩)
        ((Finset.le_sup (Finset.mem_univ j)).trans (Nat.le_succ _))
    obtain ⟨H'⟩ := (nonempty_homotopy_smul_id_zero_iff _ P).mpr hP'
    have H'' := (ModuleCat.extendScalars.{u, u, u} φ).mapHomotopy H'
    have eq1 : φ (x j) ^ w • 𝟙 PC =
        ((ModuleCat.extendScalars.{u, u, u} φ).mapHomologicalComplex _).map (x j ^ w • 𝟙 P) := by
      rw [← map_pow]
      exact (baseChange_smulId φ P (x j ^ w)).symm
    refine (nonempty_homotopy_smul_id_zero_iff _ PC).mp
      ⟨(Homotopy.ofEq eq1).trans (H''.trans (Homotopy.ofEq (Functor.map_zero _ _ _)))⟩
  -- (Supp)：共通の冪だけを使う。零作用の錐では追加の冪は不要。
  let c : Fin h → C := fun k ↦ φ (x k) ^ w
  have hJc : J ≤ (Ideal.span (Set.range c)).radical :=
    le_radical_span_pow (φ ∘ x) hJ w
  have hz : ∀ q : ℕ, 0 < q → lam.len (koszulHomologySelf c q) = 0 := by
    have heq : c = fun k ↦ φ (x k ^ w) := by funext k; simp [c]
    rw [heq]
    exact hzero w hw
  have hperfect : strictlyPerfectComplex R P := by
    refine ⟨⟨-(d : ℤ), 0, ?_, ?_⟩, fun q ↦ ?_⟩
    · rw [CochainComplex.isStrictlyGE_iff]
      exact hlen
    · rw [CochainComplex.isStrictlyLE_iff]
      exact hP.isZero_X
    · have := hfree q
      exact ⟨hfin q, Module.Projective.of_free⟩
  -- (Kos_d) の確認と共通の反復錐定理により消滅する。
  rw [lam.len_congr _ _ (torIsoCochain φ hP i).toLinearEquiv]
  exact LengthAlgebra.lambdaHomology_projective_vanishing lam hfg c hJc hz PC
    (strictlyPerfectComplex_baseChange φ P hperfect)
    (fun j ↦ (nonempty_homotopy_smul_id_zero_iff _ PC).mpr (hkill j))
    (-(d : ℤ)) 0
    (fun q hq ↦ (ModuleCat.extendScalars φ).map_isZero
      (hq.elim (hlen q) (hP.isZero_X q))) (-(i : ℤ)) (Or.inl (by omega))

end ParamQuot

end SerrePositivity

end ParameterQuotientTorBoundPart
