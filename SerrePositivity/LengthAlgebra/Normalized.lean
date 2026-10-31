module

public import SerrePositivity.LengthAlgebra.Core
public import Mathlib.Algebra.Colimit.Module
public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.Topology.Instances.ENNReal.Lemmas
public import Mathlib.Algebra.Algebra.RestrictScalars
public import SerrePositivity.CommutativeAlgebra.Length.Basic
public import SerrePositivity.CommutativeAlgebra.ConductorQuotient
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.TensorProduct.Quotient

/-! # 正規化長さの係数制限・上限の性質・テンソルの評価

## 概要

環準同型に沿った正規化長さの係数制限 `comap`、任意の加群の長さが有限生成部分加群の長さの上限であるという性質 `HasSup`（論文 Lemma 2.3 の (2.3)、Lemma 2.4 の一般形）とその係数制限での保存、有限長加群 N について λ(C ⊗_D N) ≤ ℓ_D(N) · λ(C ⊗_D (D/m_D))（論文 Corollary 2.6 の周辺）を与える。

## 方針

小さい環上の有限生成部分加群を、その生成元が大きい環上で張る部分加群へ拡大して上限を比べる。

## 規約

`NormalizedLength.comap` は CLMST が `lam.comap f _ le_rfl` の形で使うので変えない。環準同型の有限性や全射性は要らない。複体を使わないので PerfectComplex から LengthAlgebra へ移した（refactor-plan §4.2.1）。

## 使われ方

LengthAlgebra の全体、CLMST、Paper の長さ代数。
-/

@[expose] public noncomputable section

universe u v

section NormalizedLengthComapPart

open scoped ENNReal

namespace SerrePositivity

variable {Λ C : Type u} [CommRing Λ] [CommRing C] (f : Λ →+* C) {J : Ideal Λ} {J' : Ideal C}

/-- `J.map f ≤ J'` なら、`J'` のある冪で消える `C` 加群 `M` は、`f` で `Λ` 加群とみると
`J` の同じ冪で消える。 -/
lemma IsPowTorsion.comap (h : J.map f ≤ J') (M : Type u) [AddCommGroup M] [Module C M]
    (hM : IsPowTorsion J' M) :
    letI := Module.compHom M f
    IsPowTorsion J M := by
  let := Module.compHom M f
  obtain ⟨n, hn⟩ := hM
  refine ⟨n, fun x a ↦ ?_⟩
  have ha : f a ∈ J' ^ n := by
    have : f a ∈ (J ^ n).map f := Ideal.mem_map_of_mem f a.2
    rw [Ideal.map_pow] at this
    exact Ideal.pow_right_mono h n this
  exact hn (a := ⟨f a, ha⟩)

namespace NormalizedLength

/-- 正規化長さの係数制限：`C` 加群 `M` を `f : Λ →+* C` で `Λ` 加群とみて `lam` で測る。
加法性の定義域は `J.map f ≤ J'` をみたす `J'` 冪ねじれ加群。 -/
def comap (lam : NormalizedLength Λ J) (J' : Ideal C) (h : J.map f ≤ J') :
    NormalizedLength C J' where
  len M _ _ := letI := Module.compHom M f; lam.len M
  len_eq_zero_of_subsingleton M _ _ _ := by
    let := Module.compHom M f
    exact lam.len_eq_zero_of_subsingleton M
  len_congr M N _ _ _ _ e := by
    let := Module.compHom M f
    let := Module.compHom N f
    exact lam.len_congr M N
      { e with map_smul' := fun a x ↦ e.map_smul (f a) x }
  len_add_of_exact M₁ M₂ M₃ _ _ _ _ _ _ g₁ g₂ h₁ h₂ hex hM₂ := by
    let := Module.compHom M₁ f
    let := Module.compHom M₂ f
    let := Module.compHom M₃ f
    exact lam.len_add_of_exact M₁ M₂ M₃
      { g₁ with map_smul' := fun a x ↦ g₁.map_smul (f a) x }
      { g₂ with map_smul' := fun a x ↦ g₂.map_smul (f a) x }
      h₁ h₂ hex (IsPowTorsion.comap f h M₂ hM₂)

/-- `comap` は値を変えない：`C` 加群 `M` の長さは、`Λ` 加群とみた `M` の `lam` での長さ。 -/
@[simp] lemma comap_len (lam : NormalizedLength Λ J) (J' : Ideal C) (h : J.map f ≤ J')
    (M : Type u) [AddCommGroup M] [Module C M] :
    (lam.comap f J' h).len M = (letI := Module.compHom M f; lam.len M) := rfl

end NormalizedLength

end SerrePositivity

end NormalizedLengthComapPart

section SupPropertyPart

open scoped ENNReal DirectSum

namespace SerrePositivity

namespace NormalizedLength

variable {C : Type u} [CommRing C] {J : Ideal C} (lam : NormalizedLength C J)

/-- 上限の性質 (2.3)：`J` 冪ねじれの `M` について `λ(M)` は有限生成部分加群の長さの上限。 -/
def HasSup : Prop :=
  ∀ (M : Type u) [AddCommGroup M] [Module C M], IsPowTorsion J M →
    lam.len M = ⨆ (N : Submodule C M) (_ : N.FG), lam.len N

variable {lam}
variable {M : Type u} [AddCommGroup M] [Module C M]

/-- 上限の性質のもとで、`λ(M) ≤ c` は「すべての有限生成部分加群で `λ ≤ c`」と同値。 -/
lemma len_le_iff_fg (hsup : lam.HasSup) (hM : IsPowTorsion J M) (c : ℝ≥0∞) :
    lam.len M ≤ c ↔ ∀ N : Submodule C M, N.FG → lam.len N ≤ c := by
  rw [hsup M hM]
  simp only [iSup_le_iff]

/-- 上限の性質のもとで、`c < λ(M)` なら `c < λ(N)` となる有限生成部分加群 `N` がある。 -/
lemma exists_fg_lt (hsup : lam.HasSup) (hM : IsPowTorsion J M) {c : ℝ≥0∞}
    (hc : c < lam.len M) : ∃ N : Submodule C M, N.FG ∧ c < lam.len N := by
  by_contra hcon
  simp only [not_exists, not_and, not_lt] at hcon
  exact absurd ((len_le_iff_fg hsup hM c).mpr hcon) (not_le.mpr hc)

/-! ## 有限個の和 -/

/-- `λ(A ⊔ B) ≤ λ(A) + λ(B)`：`A × B → A ⊔ B` は全射で、`λ(A × B) = λ(A) + λ(B)`。 -/
lemma len_sup_le (hM : IsPowTorsion J M) (A B : Submodule C M) :
    lam.len (A ⊔ B : Submodule C M) ≤ lam.len A + lam.len B := by
  -- `A × B → A ⊔ B`
  let g : (A × B) →ₗ[C] (A ⊔ B : Submodule C M) :=
    LinearMap.codRestrict _ (A.subtype.comp (LinearMap.fst C A B) +
      B.subtype.comp (LinearMap.snd C A B)) (fun x ↦ by
        simp only [LinearMap.add_apply, LinearMap.comp_apply, Submodule.subtype_apply]
        exact Submodule.add_mem_sup x.1.2 x.2.2)
  have hg : Function.Surjective g := by
    rintro ⟨x, hx⟩
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hx
    exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), rfl⟩
  have hprod : IsPowTorsion J (A × B) := by
    obtain ⟨n, hn⟩ := hM
    exact ⟨n, fun x a ↦ Prod.ext (Subtype.ext (hn (x := x.1) (a := a)))
      (Subtype.ext (hn (x := x.2) (a := a)))⟩
  refine (lam.len_le_of_surjective g hg hprod).trans (le_of_eq ?_)
  exact lam.len_add_of_exact A (A × B) B (LinearMap.inl C A B) (LinearMap.snd C A B)
    LinearMap.inl_injective LinearMap.snd_surjective
    (LinearMap.exact_iff.mpr (LinearMap.range_inl C A B).symm) hprod

/-- 有限個の部分加群の和の長さは、長さの和以下。 -/
lemma len_finset_sup_le (hM : IsPowTorsion J M) {ι : Type*} (s : Finset ι)
    (V : ι → Submodule C M) :
    lam.len (⨆ i ∈ s, V i : Submodule C M) ≤ ∑ i ∈ s, lam.len (V i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have h : (⨆ i ∈ (∅ : Finset ι), V i : Submodule C M) = ⊥ := by simp
    rw [h, Finset.sum_empty]
    exact le_of_eq (lam.len_eq_zero_of_subsingleton _)
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.iSup_insert]
    exact (len_sup_le hM _ _).trans (add_le_add le_rfl ih)

/-! ## 和・直和 -/

/-- 部分加群の族で各 `λ(V_i) = 0` なら `λ(⨆ V_i) = 0`。有限生成部分加群は有限個の和に入る。 -/
theorem len_iSup_eq_zero (hsup : lam.HasSup) (hM : IsPowTorsion J M) {ι : Type*}
    (V : ι → Submodule C M) (hV : ∀ i, lam.len (V i) = 0) :
    lam.len (⨆ i, V i : Submodule C M) = 0 := by
  refine le_antisymm ?_ zero_le
  rw [len_le_iff_fg hsup (hM.submodule _)]
  intro N hN
  -- `N` を `⨆ V_i` の部分加群から `M` の部分加群に移す
  let N' : Submodule C M := N.map (⨆ i, V i : Submodule C M).subtype
  have hN' : N'.FG := hN.map _
  have hle : N' ≤ ⨆ i, V i := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  obtain ⟨s, hs⟩ := ((Submodule.fg_iff_compact N').mp hN').exists_finset_of_le_iSup V hle
  have h1 : lam.len N = lam.len N' :=
    lam.len_congr _ _ (Submodule.equivMapOfInjective _ (Submodule.subtype_injective _) N)
  have h2 : lam.len N' ≤ lam.len (⨆ i ∈ s, V i : Submodule C M) :=
    lam.len_le_of_injective (Submodule.inclusion hs) (Submodule.inclusion_injective hs)
      (hM.submodule _)
  have h3 : lam.len (⨆ i ∈ s, V i : Submodule C M) = 0 := by
    refine le_antisymm ((len_finset_sup_le hM s V).trans (le_of_eq ?_)) zero_le
    exact Finset.sum_eq_zero fun i _ ↦ hV i
  rw [h1]
  exact h2.trans (le_of_eq h3)

/-- 直和：各 `V_i` が `J^n` で消え `λ(V_i) = 0` なら `λ(⨁ V_i) = 0`。 -/
theorem len_directSum_eq_zero (hsup : lam.HasSup) {ι : Type u}
    (V : ι → Type u) [∀ i, AddCommGroup (V i)] [∀ i, Module C (V i)]
    (n : ℕ) (hn : ∀ i, Module.IsTorsionBySet C (V i) (J ^ n : Ideal C))
    (hV : ∀ i, lam.len (V i) = 0) : lam.len (⨁ i, V i) = 0 := by
  classical
  have htor : IsPowTorsion J (⨁ i, V i) := by
    refine ⟨n, fun x a ↦ ?_⟩
    refine DirectSum.induction_on x (by simp) (fun i y ↦ ?_)
      (fun x y hx hy ↦ by rw [smul_add, hx, hy, add_zero])
    rw [← DirectSum.lof_eq_of C, ← LinearMap.map_smul]
    have : (a : C) • y = 0 := hn i (x := y) (a := a)
    rw [this, LinearMap.map_zero]
  -- `⨁ V_i` は `lof i` の像の和
  have htop : (⨆ i, LinearMap.range (DirectSum.lof C ι V i)) = ⊤ := by
    rw [eq_top_iff]
    rintro x -
    refine DirectSum.induction_on x (zero_mem _) (fun i y ↦ ?_) (fun x y hx hy ↦ add_mem hx hy)
    rw [← DirectSum.lof_eq_of C]
    exact Submodule.mem_iSup_of_mem i (LinearMap.mem_range_self _ y)
  have h0 : ∀ i, lam.len (LinearMap.range (DirectSum.lof C ι V i)) = 0 := fun i ↦ by
    refine le_antisymm ?_ zero_le
    rw [← hV i]
    exact lam.len_le_of_surjective (DirectSum.lof C ι V i).rangeRestrict
      (LinearMap.surjective_rangeRestrict _) ⟨n, hn i⟩
  have := len_iSup_eq_zero hsup htor _ h0
  rw [htop] at this
  rw [← this]
  exact lam.len_congr _ _ Submodule.topEquiv.symm

/-! ## 有向な族と直極限 -/

/-- 有向な部分加群の族（増大列）では `λ(⨆ V_i) = ⨆ λ(V_i)`。有限生成部分加群はどれかの `V_i` に
入る。 -/
theorem len_iSup_of_directed (hsup : lam.HasSup) (hM : IsPowTorsion J M) {ι : Type*}
    [Nonempty ι] (V : ι → Submodule C M) (hdir : Directed (· ≤ ·) V) :
    lam.len (⨆ i, V i : Submodule C M) = ⨆ i, lam.len (V i) := by
  refine le_antisymm ?_ (iSup_le fun i ↦ lam.len_le_of_injective
    (Submodule.inclusion (le_iSup V i)) (Submodule.inclusion_injective _) (hM.submodule _))
  rw [len_le_iff_fg hsup (hM.submodule _)]
  intro N hN
  let N' : Submodule C M := N.map (⨆ i, V i : Submodule C M).subtype
  have hN' : N'.FG := hN.map _
  have hle : N' ≤ ⨆ i, V i := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  obtain ⟨_, ⟨i, rfl⟩, hi⟩ := (isCompactElement_iff_le_of_directed_sSup_le N').mp
    ((Submodule.fg_iff_compact N').mp hN') (Set.range V) (Set.range_nonempty V)
    (directedOn_range.mpr hdir) (by rwa [sSup_range])
  have h1 : lam.len N = lam.len N' :=
    lam.len_congr _ _ (Submodule.equivMapOfInjective _ (Submodule.subtype_injective _) N)
  rw [h1]
  exact (lam.len_le_of_injective (Submodule.inclusion hi) (Submodule.inclusion_injective hi)
    (hM.submodule _)).trans (le_iSup (fun i ↦ lam.len (V i)) i)

/-- 写像の像が有向に増大して全体を覆い、各始域の長さが零へ収束すれば全体の長さは零。
共通の消去冪から全体の冪ねじれを導く。添字の宇宙は加群の宇宙と独立でよい。 -/
theorem len_eq_zero_of_directed_cover (hsup : lam.HasSup) {ι : Type*} [Preorder ι]
    [IsDirectedOrder ι] [Nonempty ι] (G : ι → Type u)
    [∀ i, AddCommGroup (G i)] [∀ i, Module C (G i)]
    (g : ∀ i, G i →ₗ[C] M)
    (hmono : Monotone (fun i ↦ LinearMap.range (g i)))
    (hcover : ∀ x : M, ∃ i y, g i y = x)
    (n : ℕ) (hn : ∀ i, Module.IsTorsionBySet C (G i) (J ^ n : Ideal C))
    (hlim : Filter.Tendsto (fun i ↦ lam.len (G i)) Filter.atTop (nhds 0)) :
    lam.len M = 0 := by
  have htor : IsPowTorsion J M := by
    refine ⟨n, fun x a ↦ ?_⟩
    obtain ⟨i, y, rfl⟩ := hcover x
    rw [← map_smul, hn i (x := y) (a := a), map_zero]
  let W : ι → Submodule C M := fun i ↦ LinearMap.range (g i)
  have hle : ∀ i j, i ≤ j → lam.len (W i) ≤ lam.len (G j) := fun i j hij ↦
    (lam.len_le_of_injective (Submodule.inclusion (hmono hij))
      (Submodule.inclusion_injective _) (htor.submodule _)).trans
      (lam.len_le_of_surjective (g j).rangeRestrict
        (LinearMap.surjective_rangeRestrict _) ⟨n, hn j⟩)
  have hW : ∀ i, lam.len (W i) = 0 := by
    intro i
    refine le_antisymm ?_ zero_le
    refine ENNReal.le_of_forall_pos_le_add fun ε hε _ ↦ ?_
    rw [zero_add]
    obtain ⟨j₀, hj₀⟩ := Filter.eventually_atTop.mp (ENNReal.tendsto_nhds_zero.mp hlim ε
      (by exact_mod_cast hε))
    obtain ⟨k, hik, hjk⟩ := directed_of (· ≤ ·) i j₀
    exact (hle i k hik).trans (hj₀ k hjk)
  have htop : (⨆ i, W i) = ⊤ := by
    rw [eq_top_iff]
    rintro x -
    obtain ⟨i, y, rfl⟩ := hcover x
    exact Submodule.mem_iSup_of_mem i ⟨y, rfl⟩
  have he := len_iSup_eq_zero hsup htor W hW
  rw [htop] at he
  rw [← he]
  exact lam.len_congr _ _ Submodule.topEquiv.symm

/-- 直極限：各 `G_i` が `J^n` で消え、`λ(G_i) → 0` なら `λ(lim→ G_i) = 0`。遷移写像の単射性は
要らない。各段の像 `W_i = im(of i)` は `j ≥ i` で `W_i ⊆ W_j` なので `λ(W_i) ≤ λ(G_j)`、
よって `λ(W_i) = 0`。直極限は `⨆ W_i` なので `len_iSup_eq_zero`。 -/
theorem len_directLimit_eq_zero_of_tendsto (hsup : lam.HasSup) {ι : Type u} [Preorder ι]
    [IsDirectedOrder ι] [Nonempty ι] [DecidableEq ι] (G : ι → Type u)
    [∀ i, AddCommGroup (G i)] [∀ i, Module C (G i)] (f : ∀ i j, i ≤ j → G i →ₗ[C] G j)
    (n : ℕ) (hn : ∀ i, Module.IsTorsionBySet C (G i) (J ^ n : Ideal C))
    (hlim : Filter.Tendsto (fun i ↦ lam.len (G i)) Filter.atTop (nhds 0)) :
    lam.len (Module.DirectLimit G f) = 0 := by
  apply len_eq_zero_of_directed_cover hsup G (Module.DirectLimit.of C ι G f)
    ?_ Module.DirectLimit.exists_of n hn hlim
  rintro i j hij _ ⟨x, rfl⟩
  exact ⟨f i j hij x, Module.DirectLimit.of_f⟩

end NormalizedLength

end SerrePositivity

end SupPropertyPart

section SupPropertyComapPart

namespace SerrePositivity.NormalizedLength
open scoped ENNReal

variable {Λ C : Type u} [CommRing Λ] [CommRing C] {J : Ideal Λ}
    {lam : NormalizedLength Λ J}

/-- 正規化長さの上限の性質は、任意の環準同型に沿った係数制限で保たれる。 -/
theorem HasSup.comap (hsup : lam.HasSup) (f : Λ →+* C) (J' : Ideal C)
    (hJ : J.map f ≤ J') : (lam.comap f J' hJ).HasSup := by
  intro M _ _ hM
  let : Algebra Λ C := f.toAlgebra
  let : Module Λ M := Module.compHom M f
  let : IsScalarTower Λ C M := IsScalarTower.of_compHom Λ C M
  have hMR : IsPowTorsion J M := IsPowTorsion.comap f hJ M hM
  change lam.len M = ⨆ (V : Submodule C M) (_ : V.FG), (lam.comap f J' hJ).len V
  refine le_antisymm ?_ ?_
  · rw [hsup M hMR]
    refine iSup₂_le fun N hN ↦ ?_
    let V : Submodule C M := Submodule.span C (N : Set M)
    let : Module Λ V := Module.compHom V f
    let g : N →ₗ[Λ] V :=
      { toFun := fun n ↦ ⟨n, Submodule.subset_span n.property⟩
        map_add' := fun _ _ ↦ Subtype.ext rfl
        map_smul' := fun _ _ ↦ Subtype.ext rfl }
    have hg : Function.Injective g := fun _ _ h ↦
      Subtype.ext (congrArg (fun v : V ↦ (v : M)) h)
    have hVR : IsPowTorsion J V := IsPowTorsion.comap f hJ V (hM.submodule V)
    have hle : lam.len N ≤ (lam.comap f J' hJ).len V :=
      lam.len_le_of_injective g hg hVR
    exact hle.trans (le_iSup₂_of_le V hN.span le_rfl)
  · refine iSup₂_le fun V _ ↦ ?_
    exact (lam.comap f J' hJ).len_le_of_injective V.subtype V.injective_subtype hM

end SerrePositivity.NormalizedLength

end SupPropertyComapPart

section QuotientLengthPart

open IsLocalRing TensorProduct
open scoped ENNReal

namespace SerrePositivity

variable {D C : Type u} [CommRing D] [CommRing C] [Algebra D C]

/-- 係数環のイデアルの冪で消える商は、代数を拡大しても同じ冪で消える。
元の商で単位元を消すことから、係数の像がイデアルに入ると分かる。
平坦性や有限生成性は必要ない。 -/
lemma isPowTorsion_quotient_extension (R : Type u) [CommRing R]
    [Algebra R D] [Algebra R C] [IsScalarTower R D C]
    (J : Ideal R) (I : Ideal D) (hI : IsPowTorsion J (D ⧸ I)) :
    IsPowTorsion J (C ⧸ I.map (algebraMap D C)) := by
  obtain ⟨k, hk⟩ := hI
  refine ⟨k, ?_⟩
  rw [Module.isTorsionBySet_iff_subset_annihilator] at hk ⊢
  intro r hr
  simp only [SetLike.mem_coe, Module.mem_annihilator]
  intro x
  obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective x
  have hz := (Module.mem_annihilator.mp (hk hr)) (1 : D ⧸ I)
  have hm : algebraMap R D r ∈ I := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    simpa only [Algebra.smul_def, mul_one, IsScalarTower.algebraMap_apply R D (D ⧸ I),
      Ideal.Quotient.algebraMap_eq] using hz
  rw [Algebra.smul_def, ← Ideal.Quotient.mk_algebraMap, ← map_mul]
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  rw [IsScalarTower.algebraMap_apply R D C]
  exact Ideal.mul_mem_right c _ (Ideal.mem_map_of_mem _ hm)

/-- `D` 加群 `M` がイデアル `J` の `n` 乗で消えるなら `C ⊗_D M` は `(J C)^n` で消える。 -/
lemma isPowTorsion_tensorProduct_of_isTorsionBySet (J : Ideal D) (M : Type u) [AddCommGroup M]
    [Module D M] {n : ℕ} (hM : Module.IsTorsionBySet D M (J ^ n : Ideal D)) :
    IsPowTorsion (J.map (algebraMap D C)) (C ⊗[D] M) := by
  refine ⟨n, ?_⟩
  rw [Module.isTorsionBySet_iff_subset_annihilator, ← Ideal.map_pow, SetLike.coe_subset_coe,
    Ideal.map_le_iff_le_comap]
  intro a ha
  rw [Ideal.mem_comap, Module.mem_annihilator]
  intro x
  refine TensorProduct.inductionOn x (fun c m ↦ ?_)
    (fun x y hx hy ↦ by rw [smul_add, hx, hy, add_zero])
  rw [algebraMap_smul, ← TensorProduct.tmul_smul]
  have : a • m = 0 := hM (x := m) (a := ⟨a, ha⟩)
  rw [this, TensorProduct.tmul_zero]

/-- 共通分母による商写像の核の正規化長さの評価。
長さを測る基底 `R` は `D` と別に取れるので、塔上の正規化長さにも適用できる。
`g` 倍写像の余核を `D/(I,g)` と同定して、右辺を通常の商の長さで表す。 -/
theorem len_ker_quotientToExtension_le (R : Type u) [CommRing R]
    [Algebra R D] [Algebra R C] [IsScalarTower R D C]
    {J : Ideal R} (lam : NormalizedLength R J)
    (hinj : Function.Injective (algebraMap D C)) (I : Ideal D) (g : D)
    (hg : ∀ c : C, ∃ d : D, algebraMap D C d = algebraMap D C g * c)
    (htors : IsPowTorsion J (D ⧸ I)) (hfinite : lam.len (D ⧸ I) ≠ ⊤) :
    lam.len (LinearMap.ker ((quotientToExtension (C := C) I).toLinearMap.restrictScalars R)) ≤
      lam.len (D ⧸ (I ⊔ Ideal.span {g})) := by
  rw [← lam.len_congr _ _ (quotientSmulCokerEquiv R I g)]
  apply lam.len_ker_le_len_coker_of_ker_le _ _ htors hfinite
  intro x hx
  exact smul_eq_zero_of_quotientToExtension_eq_zero hinj I g hg x hx

variable [IsLocalRing D]

/-- `D` 加群 `M` が `m_D^n` で消えるなら `C ⊗_D M` は `(m_D C)^n` で消える。 -/
lemma isPowTorsion_tensorProduct (M : Type u) [AddCommGroup M] [Module D M] {n : ℕ}
    (hM : Module.IsTorsionBySet D M ((maximalIdeal D) ^ n : Ideal D)) :
    IsPowTorsion ((maximalIdeal D).map (algebraMap D C)) (C ⊗[D] M) :=
  isPowTorsion_tensorProduct_of_isTorsionBySet (maximalIdeal D) M hM

/-- 有限長 `D` 加群 `M` について `C ⊗_D M` は `m_D C` 冪ねじれ。 -/
lemma isPowTorsion_tensorProduct_of_isFiniteLength (M : Type u) [AddCommGroup M] [Module D M]
    (hM : IsFiniteLength D M) :
    IsPowTorsion ((maximalIdeal D).map (algebraMap D C)) (C ⊗[D] M) := by
  obtain ⟨n, hn⟩ := IsFiniteLength.exists_isTorsionBySet_maximalIdeal_pow hM
  exact isPowTorsion_tensorProduct M hn

variable (lam : NormalizedLength C ((maximalIdeal D).map (algebraMap D C)))

/-- **組成列による評価**：有限長 `D` 加群 `M` で `λ(C ⊗_D M) ≤ ℓ_D(M) · λ(C ⊗_D (D/m_D))`。 -/
theorem len_tensorProduct_le_length_mul (M : Type u) [AddCommGroup M] [Module D M]
    (hM : IsFiniteLength D M) :
    lam.len (C ⊗[D] M) ≤
      (Module.length D M : ℝ≥0∞) * lam.len (C ⊗[D] (D ⧸ maximalIdeal D)) := by
  induction hM with
  | of_subsingleton =>
    rename_i M _ _ _
    have : Subsingleton (C ⊗[D] M) := inferInstance
    rw [lam.len_eq_zero_of_subsingleton]
    exact zero_le
  | @of_simple_quotient M _ _ N _ hN ih =>
    have hMfl : IsFiniteLength D M := IsFiniteLength.of_simple_quotient hN
    have hQfl : IsFiniteLength D (M ⧸ N) := hMfl.of_surjective N.mkQ_surjective
    -- `C ⊗ N → C ⊗ M → C ⊗ (M/N)` は完全
    have hex : Function.Exact (N.subtype.baseChange C) (N.mkQ.baseChange C) := by
      have := lTensor_exact C (LinearMap.exact_subtype_mkQ N) N.mkQ_surjective
      rwa [← LinearMap.baseChange_eq_lTensor, ← LinearMap.baseChange_eq_lTensor] at this
    have h1 := lam.len_le_add_of_exact _ _ hex
      (isPowTorsion_tensorProduct_of_isFiniteLength N hN)
      (isPowTorsion_tensorProduct_of_isFiniteLength M hMfl)
      (isPowTorsion_tensorProduct_of_isFiniteLength _ hQfl)
    -- `C ⊗ (M/N) ≃ C ⊗ (D/m)`
    obtain ⟨e⟩ := IsSimpleModule.nonempty_linearEquiv_quotient_maximalIdeal (A := D) (M := M ⧸ N)
    have h2 : lam.len (C ⊗[D] (M ⧸ N)) = lam.len (C ⊗[D] (D ⧸ maximalIdeal D)) :=
      lam.len_congr _ _ (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl C C) e)
    rw [h2] at h1
    refine h1.trans ?_
    rw [Module.length_eq_succ_of_isSimpleModule_quotient N, ENat.toENNReal_add,
      ENat.toENNReal_one, add_mul, one_mul]
    exact add_le_add ih le_rfl

/-- `N = D/H` の形：`λ(C/HC) ≤ ℓ_D(D/H) · λ(C/m_D C)`。 -/
theorem len_quotient_map_le_length_mul (H : Ideal D) (hH : IsFiniteLength D (D ⧸ H)) :
    lam.len (C ⧸ H.map (algebraMap D C)) ≤
      (Module.length D (D ⧸ H) : ℝ≥0∞) *
        lam.len (C ⧸ (maximalIdeal D).map (algebraMap D C)) := by
  have e1 := lam.len_congr _ _
    (Algebra.TensorProduct.quotIdealMapEquivTensorQuot C H).toLinearEquiv
  have e2 := lam.len_congr _ _
    (Algebra.TensorProduct.quotIdealMapEquivTensorQuot C (maximalIdeal D)).toLinearEquiv
  rw [e1, e2]
  exact len_tensorProduct_le_length_mul lam _ hH

/-- `0 < λ(C/HC)` で `ℓ(D/H) < ∞` なら `0 < λ(C/m_D C)`（Corollary 2.6 (3) の最後の一歩）。 -/
theorem len_quotient_maximalIdeal_pos (H : Ideal D) (hH : IsFiniteLength D (D ⧸ H))
    (hpos : 0 < lam.len (C ⧸ H.map (algebraMap D C))) :
    0 < lam.len (C ⧸ (maximalIdeal D).map (algebraMap D C)) := by
  by_contra h0
  rw [not_lt, nonpos_iff_eq_zero] at h0
  have := len_quotient_map_le_length_mul lam H hH
  rw [h0, mul_zero] at this
  exact absurd (le_antisymm this zero_le) hpos.ne'

end SerrePositivity

end QuotientLengthPart
