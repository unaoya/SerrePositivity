module

public import Mathlib.RingTheory.Noetherian.Basic
public import Mathlib.Data.Fin.Tuple.Basic

/-!
# 有限層別に用いる noetherian 帰納

## 概要
真のイデアルごとに次の層の元を選ぶ操作から、有限個の元による層別を構成する。

## 方針
元を一つ加えるたびにイデアルが真に増大することを使う。

## 規約
第 i 層のイデアルは、それより前の元が生成するイデアル。

## 使われ方
一般点を含む主開集合を順に取り除く層別の有限性。
-/

@[expose] public section
noncomputable section
universe u

namespace SerrePositivity.CommutativeAlgebra

/-- 第 i 層より前に現れる元だけが生成するイデアル。初層では零イデアル。 -/
def earlierIdeal {R : Type u} [CommRing R] {n : ℕ} (g : Fin n → R) (i : Fin n) : Ideal R :=
  Ideal.span (g '' {j | j < i})

@[simp]
theorem earlierIdeal_cons_zero {R : Type u} [CommRing R] {n : ℕ}
    (x : R) (g : Fin n → R) : earlierIdeal (Fin.cons x g) 0 = ⊥ := by
  simp [earlierIdeal]

@[simp]
theorem earlierIdeal_cons_succ {R : Type u} [CommRing R] {n : ℕ}
    (x : R) (g : Fin n → R) (i : Fin n) :
    earlierIdeal (Fin.cons x g) i.succ = Ideal.span {x} ⊔ earlierIdeal g i := by
  have he : Fin.cons x g '' {j | j < i.succ} = insert x (g '' {j | j < i}) := by
    ext y
    constructor
    · rintro ⟨j, hj, rfl⟩
      refine Fin.cases ?_ (fun j hj ↦ ?_) j hj
      · intro _
        exact Set.mem_insert x _
      · exact Set.mem_insert_of_mem _ ⟨j, Fin.succ_lt_succ_iff.mp hj, rfl⟩
    · rintro (rfl | ⟨j, hj, rfl⟩)
      · exact ⟨0, Fin.zero_lt_succ i, rfl⟩
      · exact ⟨j.succ, Fin.succ_lt_succ_iff.mpr hj, rfl⟩
  rw [earlierIdeal, he, Ideal.span_insert]
  rfl

/-- 真のイデアルの外に次の層の元を選べれば、有限列で単位イデアルに到達する。 -/
theorem exists_finite_ideal_filtration {R : Type u} [CommRing R] [IsNoetherianRing R]
    (P : Ideal R → R → Prop)
    (hstep : ∀ I : Ideal R, I ≠ ⊤ → ∃ x : R, x ∉ I ∧ P I x) (I : Ideal R) :
    ∃ (n : ℕ) (g : Fin n → R), I ⊔ Ideal.span (Set.range g) = ⊤ ∧
      ∀ i, P (I ⊔ earlierIdeal g i) (g i) := by
  classical
  induction I using WellFoundedGT.induction with
  | ind I ih =>
    by_cases hI : I = ⊤
    · refine ⟨0, Fin.elim0, ?_, fun i ↦ Fin.elim0 i⟩
      simp [hI]
    · obtain ⟨x, hx, hP⟩ := hstep I hI
      let J := I ⊔ Ideal.span {x}
      have hIJ : I < J := lt_of_le_of_ne le_sup_left (by
        intro he
        exact hx (he.symm ▸ (show x ∈ J from
          le_sup_right (Ideal.subset_span (Set.mem_singleton x)))))
      obtain ⟨n, g, hg, hPg⟩ := ih J hIJ
      refine ⟨n + 1, Fin.cons x g, ?_, ?_⟩
      · simpa [Fin.range_cons, Ideal.span_insert, sup_assoc, J] using hg
      · intro i
        refine Fin.cases ?_ (fun j ↦ ?_) i
        · simpa using hP
        · simpa [sup_assoc, J] using hPg j

end SerrePositivity.CommutativeAlgebra
