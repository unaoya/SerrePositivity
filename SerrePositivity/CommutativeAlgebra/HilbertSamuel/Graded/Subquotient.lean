module

public import Mathlib.Algebra.DirectSum.Decomposition
public import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Submodule
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.Algebra.Exact.Basic

/-! # 次数分解の部分加群・商加群への降下と、次数をずらす写像

## 概要

次数分解 `N : ℕ → Submodule R M`（`DirectSum.Decomposition`）について、成分射影 `gradeProjection`、
同次な部分加群・商加群の次数分解（`isInternal_submoduleGrade`・`isInternal_quotientGrade`）を与える。
さらに二つの次数付き加群の間で次数を `d` 上げる線形写像 `F` について、射影との可換性、核と像の斉次性、
各次数の写像 `componentMap` と余核の成分 `quotientComponent` の完全性を一度だけ示す。

## 方針

射影との可換性は分解の各成分で確かめる（`DirectSum.decompose_lhom_ext`）。核・像・完全性はすべてそこから従う。

## 規約

次数一の作用（`d = 1`、同じ加群）、任意次数の斉次関係、Koszul 複体の微分（二つの加群、`d = 1`）、
次数を保つ全射（`d = 0`）はすべてこの節の特殊化として使う。名前空間は `HilbertSerre`。

## 使われ方

Hilbert 級数と Hilbert–Serre（`HilbertSamuel/Graded/HilbertSeries`）、斉次関係の増大
（`Graded/PolynomialRing`）、次数付き Koszul ホモロジー（`GradedKoszulHomology`）、KST の blowup。
-/

@[expose] public noncomputable section

universe u

namespace SerrePositivity.HilbertSerre

open DirectSum
open scoped DirectSum

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R] {M : Type u} [AddCommGroup M] [Module R M]

/-- 成分を取り出して元の加群へ入れ直す射影。 -/
def gradeProjection (N : ℕ → Submodule R M) [Decomposition N] (n : ℕ) : M →ₗ[R] M :=
  (N n).subtype.comp ((DirectSum.component R ℕ (fun n => N n) n).comp
    (DirectSum.decomposeLinearEquiv N).toLinearMap)

@[simp]
lemma gradeProjection_apply (N : ℕ → Submodule R M) [Decomposition N] (n : ℕ) (m : M) :
    gradeProjection N n m = (DirectSum.decompose N m n : M) := rfl

lemma gradeProjection_same (N : ℕ → Submodule R M) [Decomposition N] (n : ℕ)
    {m : M} (hm : m ∈ N n) : gradeProjection N n m = m :=
  DirectSum.decompose_of_mem_same N hm

lemma gradeProjection_ne (N : ℕ → Submodule R M) [Decomposition N] (n k : ℕ)
    (hkn : k ≠ n) {m : M} (hm : m ∈ N k) : gradeProjection N n m = 0 :=
  DirectSum.decompose_of_mem_ne N hm hkn

/-- 独立な射影があり、各成分が全体を生成するなら、その直和は内部直和。 -/
theorem isInternal_of_projections (N : ℕ → Submodule R M) (p : ℕ → M →ₗ[R] M)
    (hsame : ∀ n (m : N n), p n m = (m : M))
    (hzero : ∀ n k, k ≠ n → ∀ m : N k, p n m = 0)
    (hspan : iSup N = ⊤) : DirectSum.IsInternal N := by
  have hcomp (n : ℕ) : (p n).comp (DirectSum.coeLinearMap N) =
      (N n).subtype.comp (DirectSum.component R ℕ (fun n => N n) n) := by
    apply DirectSum.linearMap_ext
    intro k
    apply LinearMap.ext
    intro m
    simp only [LinearMap.comp_apply, DirectSum.coeLinearMap_lof]
    by_cases hk : k = n
    · subst k; simpa using hsame n m
    · rw [hzero n k hk m]
      change 0 = ((DirectSum.of (fun n => N n) k m) n : M)
      rw [DirectSum.of_eq_of_ne _ _ _ (Ne.symm hk)]
      rfl
  refine ⟨?_, ?_⟩
  · intro x y hxy
    apply DFinsupp.ext
    intro n
    apply Subtype.ext
    have h := congrArg (p n) hxy
    change ((p n).comp (DirectSum.coeLinearMap N)) x =
      ((p n).comp (DirectSum.coeLinearMap N)) y at h
    rw [hcomp n] at h
    exact h
  · change Function.Surjective (DirectSum.coeLinearMap N)
    rw [← LinearMap.range_eq_top, DirectSum.range_coeLinearMap]
    exact hspan

/-- 部分加群内の第 n 次成分。 -/
def submoduleGrade (N : ℕ → Submodule R M) (S : Submodule R M) (n : ℕ) :
    Submodule R S := (N n).comap S.subtype

/-- 同次な部分加群は各次数の交わりで生成される。 -/
lemma iSup_submoduleGrade_eq_top (N : ℕ → Submodule R M) [Decomposition N]
    (S : Submodule R M) (hS : S.IsHomogeneous N) :
    iSup (submoduleGrade N S) = ⊤ := by
  classical
  apply top_unique
  intro x _
  have hsum : (∑ n ∈ (DirectSum.decompose N (x : M)).support,
      (⟨(DirectSum.decompose N (x : M) n : M), hS n x.2⟩ : S)) = x := by
    apply Subtype.ext
    simpa using DirectSum.sum_support_decompose N (x : M)
  rw [← hsum]
  apply Submodule.sum_mem
  intro n _
  exact (le_iSup (submoduleGrade N S) n)
    (show _ ∈ submoduleGrade N S n from (DirectSum.decompose N (x : M) n).2)

/-- 同次な部分加群の内部直和表示。 -/
theorem isInternal_submoduleGrade (N : ℕ → Submodule R M) [Decomposition N]
    (S : Submodule R M) (hS : S.IsHomogeneous N) :
    DirectSum.IsInternal (submoduleGrade N S) := by
  let p (n : ℕ) : S →ₗ[R] S :=
    ((gradeProjection N n).comp S.subtype).codRestrict S (fun x => hS n x.2)
  apply isInternal_of_projections (submoduleGrade N S) p
  · intro n m
    apply Subtype.ext
    exact gradeProjection_same N n m.2
  · intro n k hkn m
    apply Subtype.ext
    exact gradeProjection_ne N n k hkn m.2
  · exact iSup_submoduleGrade_eq_top N S hS

/-- 商加群内の第 n 次成分。 -/
def quotientGrade (N : ℕ → Submodule R M) (S : Submodule R M) (n : ℕ) :
    Submodule R (M ⧸ S) := (N n).map S.mkQ

/-- 同次な部分加群による商の内部直和表示。 -/
theorem isInternal_quotientGrade (N : ℕ → Submodule R M) [Decomposition N]
    (S : Submodule R M) (hS : S.IsHomogeneous N) :
    DirectSum.IsInternal (quotientGrade N S) := by
  let p (n : ℕ) : M ⧸ S →ₗ[R] M ⧸ S :=
    S.mapQ S (gradeProjection N n) (fun x hx => hS n hx)
  apply isInternal_of_projections (quotientGrade N S) p
  · intro n m
    obtain ⟨x, hx, hxm⟩ := m.2
    change p n (m : M ⧸ S) = m
    rw [← hxm]
    change S.mkQ (gradeProjection N n x) = S.mkQ x
    rw [gradeProjection_same N n hx]
  · intro n k hkn m
    obtain ⟨x, hx, hxm⟩ := m.2
    change p n (m : M ⧸ S) = 0
    rw [← hxm]
    change S.mkQ (gradeProjection N n x) = 0
    rw [gradeProjection_ne N n k hkn hx, map_zero]
  · change (⨆ n, (N n).map S.mkQ) = ⊤
    rw [← Submodule.map_iSup, Decomposition.isInternal N |>.submodule_iSup_eq_top,
      Submodule.map_top, Submodule.range_mkQ]

section DegreeShift

/-! ### 次数を `d` だけ上げる線形写像

二つの次数付き加群の間で、第 `n` 次成分を第 `n + d` 次成分へ送る線形写像。次数一の作用（Hilbert–Serre）、
任意次数の斉次関係（累積長さ）、Koszul 複体の微分（GradedKoszul）、次数を保つ全射（`d = 0`）に共通の API。 -/

variable {T : Type u} [AddCommGroup T] [Module R T]
variable (NS : ℕ → Submodule R M) (NT : ℕ → Submodule R T)
variable [Decomposition NS] [Decomposition NT] (F : M →ₗ[R] T) {d : ℕ}
variable (hdegree : ∀ n, ∀ x ∈ NS n, F x ∈ NT (n + d))

include hdegree

/-- 成分射影と、次数を `d` 上げる写像の可換性。 -/
lemma gradeProjection_comp_of_degree (n : ℕ) :
    (gradeProjection NT (n + d)).comp F = F.comp (gradeProjection NS n) := by
  apply DirectSum.decompose_lhom_ext NS
  intro k
  apply LinearMap.ext
  intro x
  simp only [LinearMap.comp_apply, Submodule.coe_subtype]
  by_cases h : k = n
  · subst k
    rw [gradeProjection_same NT (n + d) (hdegree n x x.2), gradeProjection_same NS n x.2]
  · rw [gradeProjection_ne NT (n + d) (k + d) (by omega) (hdegree k x x.2),
      gradeProjection_ne NS n k h x.2, map_zero]

/-- 次数 `d` 未満の成分へは何も写らない。 -/
lemma gradeProjection_comp_eq_zero_of_lt (n : ℕ) (hn : n < d) :
    (gradeProjection NT n).comp F = 0 := by
  apply DirectSum.decompose_lhom_ext NS
  intro k
  apply LinearMap.ext
  intro x
  change gradeProjection NT n (F x) = 0
  exact gradeProjection_ne NT n (k + d) (by omega) (hdegree k x x.2)

lemma ker_isHomogeneous_of_degree : F.ker.IsHomogeneous NS := by
  intro n x hx
  change F (gradeProjection NS n x) = 0
  rw [← LinearMap.comp_apply, ← gradeProjection_comp_of_degree NS NT F hdegree]
  change gradeProjection NT (n + d) (F x) = 0
  rw [LinearMap.mem_ker.mp hx, map_zero]

lemma range_isHomogeneous_of_degree : F.range.IsHomogeneous NT := by
  intro n x hx
  obtain ⟨y, rfl⟩ := hx
  by_cases hn : d ≤ n
  · have h := DFunLike.congr_fun (gradeProjection_comp_of_degree NS NT F hdegree (n - d)) y
    rw [Nat.sub_add_cancel hn] at h
    exact ⟨gradeProjection NS (n - d) y, h.symm⟩
  · have h := DFunLike.congr_fun
      (gradeProjection_comp_eq_zero_of_lt NS NT F hdegree n (by omega)) y
    change gradeProjection NT n (F y) ∈ F.range
    rw [show gradeProjection NT n (F y) = 0 from h]
    exact Submodule.zero_mem _

omit [Decomposition NS] [Decomposition NT] in
/-- 第 `n` 次成分から第 `n + d` 次成分への写像。 -/
def componentMap (n : ℕ) : NS n →ₗ[R] NT (n + d) :=
  (F.comp (NS n).subtype).codRestrict (NT (n + d)) (fun x => hdegree n x x.2)

omit [Decomposition NS] [Decomposition NT] in
lemma componentMap_injective (hF : Function.Injective F) (n : ℕ) :
    Function.Injective (componentMap NS NT F hdegree n) := by
  intro x y h
  apply Subtype.ext
  exact hF (congrArg Subtype.val h)

omit [Decomposition NS] [Decomposition NT] in
/-- 第 `n` 次の核と、全体の核の第 `n` 次成分の一致。 -/
def kernelGradeEquiv (n : ℕ) :
    submoduleGrade NS F.ker n ≃ₗ[R] (componentMap NS NT F hdegree n).ker where
  toFun x := ⟨⟨x.1.1, x.2⟩, Subtype.ext x.1.2⟩
  invFun x := ⟨⟨x.1.1, congrArg Subtype.val x.2⟩, x.1.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit hdegree in
omit [Decomposition NS] [Decomposition NT] in
/-- 全体の余核へ写すと、第 `n` 次成分の像が余核の第 `n` 次成分になる。 -/
def quotientComponent (n : ℕ) : NT n →ₗ[R] quotientGrade NT F.range n :=
  (F.range.mkQ.comp (NT n).subtype).codRestrict _ (fun x => ⟨x, x.2, rfl⟩)

omit hdegree in
omit [Decomposition NS] [Decomposition NT] in
lemma quotientComponent_surjective (n : ℕ) :
    Function.Surjective (quotientComponent NT F n) := by
  intro y
  obtain ⟨x, hx, hxy⟩ := y.2
  exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩

lemma componentMap_quotientComponent_exact (n : ℕ) :
    Function.Exact (componentMap NS NT F hdegree n) (quotientComponent NT F (n + d)) := by
  intro x
  constructor
  · intro hx
    have hx0 : F.range.mkQ (x : T) = 0 := congrArg Subtype.val hx
    obtain ⟨y, hy⟩ := (Submodule.Quotient.mk_eq_zero _).mp hx0
    refine ⟨⟨gradeProjection NS n y, (DirectSum.decompose NS y n).2⟩, ?_⟩
    apply Subtype.ext
    have h := DFunLike.congr_fun (gradeProjection_comp_of_degree NS NT F hdegree n) y
    exact h.symm.trans (by
      change gradeProjection NT (n + d) (F y) = (x : T)
      rw [hy, gradeProjection_same NT (n + d) x.2])
  · rintro ⟨y, rfl⟩
    apply Subtype.ext
    change F.range.mkQ (F y) = 0
    exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨y, rfl⟩

/-- 次数 `d` 未満では余核の成分は元の成分そのもの。 -/
lemma quotientComponent_injective_of_lt (n : ℕ) (hn : n < d) :
    Function.Injective (quotientComponent NT F n) := by
  rw [← LinearMap.ker_eq_bot]
  apply (Submodule.eq_bot_iff _).mpr
  intro x hx
  have hx0 : F.range.mkQ (x : T) = 0 := congrArg Subtype.val hx
  obtain ⟨y, hy⟩ := (Submodule.Quotient.mk_eq_zero _).mp hx0
  apply Subtype.ext
  have h := DFunLike.congr_fun (gradeProjection_comp_eq_zero_of_lt NS NT F hdegree n hn) y
  change gradeProjection NT n (F y) = 0 at h
  rw [hy, gradeProjection_same NT n x.2] at h
  exact h

end DegreeShift

end SerrePositivity.HilbertSerre
