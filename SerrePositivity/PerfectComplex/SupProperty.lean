module

public import SerrePositivity.PerfectComplex.NormalizedLength
public import Mathlib.Algebra.Colimit.Module
public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.Topology.Instances.ENNReal.Lemmas

/-!
# 上限の性質と長さ 0 の極限（論文 Lemma 2.4 の一般形）

## 概要

論文 Lemma 2.3 の (2.3)「任意の加群の正規化長さは、有限生成部分加群の長さの上限」を、
正規化長さ `lam : NormalizedLength C J` に対する性質 `lam.HasSup` として定め、そこから
Lemma 2.4（零長さの極限）を一般の形で証明する。`J` 冪ねじれの加群について：

- 部分加群の族で各 `λ = 0` なら、その和 `⨆ V_i` も `λ = 0`（`len_iSup_eq_zero`）。
- 直和：各 `λ(V_i) = 0` なら `λ(⨁ V_i) = 0`（`len_directSum_eq_zero`）。
- 有向な族（増大列）では `λ(⨆ V_i) = ⨆ λ(V_i)`（`len_iSup_of_directed`）。
- 直極限：`λ(V_i) → 0` なら `λ(lim→ V_i) = 0`。遷移写像の単射性は要らない
  （`len_directLimit_eq_zero_of_tendsto`）。

論文の証明（p.7）どおり、有限生成部分加群が有限個の段・有限個の直和因子に入ることと、
加法性・単調性だけを使う。「すべての加群が `m_A` の固定した冪で消える」という論文の前提は、
直和・直極限では共通の冪 `n` を仮定として受け取る形で書く。

## 内容

- `HasSup`、`len_le_iff_fg`、`exists_fg_lt`。
- 有限個の和の評価 `len_sup_le`、`len_finset_sup_le`。
- 上の四つの定理。
-/

@[expose] public section

universe u v

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

/-- 直極限：各 `G_i` が `J^n` で消え、`λ(G_i) → 0` なら `λ(lim→ G_i) = 0`。遷移写像の単射性は
要らない。各段の像 `W_i = im(of i)` は `j ≥ i` で `W_i ⊆ W_j` なので `λ(W_i) ≤ λ(G_j)`、
よって `λ(W_i) = 0`。直極限は `⨆ W_i` なので `len_iSup_eq_zero`。 -/
theorem len_directLimit_eq_zero_of_tendsto (hsup : lam.HasSup) {ι : Type u} [Preorder ι]
    [IsDirectedOrder ι] [Nonempty ι] [DecidableEq ι] (G : ι → Type u)
    [∀ i, AddCommGroup (G i)] [∀ i, Module C (G i)] (f : ∀ i j, i ≤ j → G i →ₗ[C] G j)
    (n : ℕ) (hn : ∀ i, Module.IsTorsionBySet C (G i) (J ^ n : Ideal C))
    (hlim : Filter.Tendsto (fun i ↦ lam.len (G i)) Filter.atTop (nhds 0)) :
    lam.len (Module.DirectLimit G f) = 0 := by
  -- 直極限は `J^n` で消える
  have htor : IsPowTorsion J (Module.DirectLimit G f) := by
    refine ⟨n, fun z a ↦ ?_⟩
    obtain ⟨i, x, rfl⟩ := Module.DirectLimit.exists_of z
    rw [← map_smul]
    have : (a : C) • x = 0 := hn i (x := x) (a := a)
    rw [this, map_zero]
  let W : ι → Submodule C (Module.DirectLimit G f) := fun i ↦
    LinearMap.range (Module.DirectLimit.of C ι G f i)
  -- `W_i ⊆ W_j`（`i ≤ j`）
  have hmono : ∀ i j, i ≤ j → W i ≤ W j := by
    rintro i j hij _ ⟨x, rfl⟩
    exact ⟨f i j hij x, Module.DirectLimit.of_f⟩
  -- `λ(W_i) ≤ λ(G_j)`（`i ≤ j`）
  have hle : ∀ i j, i ≤ j → lam.len (W i) ≤ lam.len (G j) := fun i j hij ↦
    (lam.len_le_of_injective (Submodule.inclusion (hmono i j hij))
      (Submodule.inclusion_injective _) (htor.submodule _)).trans
      (lam.len_le_of_surjective (Module.DirectLimit.of C ι G f j).rangeRestrict
        (LinearMap.surjective_rangeRestrict _) ⟨n, hn j⟩)
  -- よって `λ(W_i) = 0`
  have hW : ∀ i, lam.len (W i) = 0 := by
    intro i
    refine le_antisymm ?_ zero_le
    refine ENNReal.le_of_forall_pos_le_add fun ε hε _ ↦ ?_
    rw [zero_add]
    obtain ⟨j₀, hj₀⟩ := Filter.eventually_atTop.mp (ENNReal.tendsto_nhds_zero.mp hlim ε
      (by exact_mod_cast hε))
    obtain ⟨k, hik, hjk⟩ := directed_of (· ≤ ·) i j₀
    exact (hle i k hik).trans (hj₀ k hjk)
  -- 直極限は `⨆ W_i`
  have htop : (⨆ i, W i) = ⊤ := by
    rw [eq_top_iff]
    rintro z -
    obtain ⟨i, x, rfl⟩ := Module.DirectLimit.exists_of z
    exact Submodule.mem_iSup_of_mem i ⟨x, rfl⟩
  have := len_iSup_eq_zero hsup htor W hW
  rw [htop] at this
  rw [← this]
  exact lam.len_congr _ _ Submodule.topEquiv.symm

end NormalizedLength

end SerrePositivity
