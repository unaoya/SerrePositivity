module

public import Mathlib.Algebra.DirectSum.Decomposition
public import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Submodule
public import Mathlib.LinearAlgebra.Isomorphisms

/-! # 次数分解の部分加群・商加群への降下

同次な部分加群について、その部分加群と商加群に実際の次数分解を構成する。
次数一の作用の核・余核を Hilbert–Serre の帰納法へ渡すための線形代数。
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

end SerrePositivity.HilbertSerre
