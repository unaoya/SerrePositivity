module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Totalization.ColumnPrimitive

/-!
# 積全複体の対角線の完全性とホモロジーの下界

## 概要
指定対角線の各行のホモロジーが零なら、同じ積全複体のホモロジーも零となる。

## 方針
有限部分の原始元を順に延長し、安定した各成分を積全複体の一つの元へまとめる。
各成分で無限和は取らず、既存の二項の全微分公式を使う。

## 規約
縦の複体の項ごとの有界性は仮定しない。原始元の選択は完全性の証明の中だけで使う。

## 使われ方
BS 著者版 Lemma 4.22 の、有限切断の尾部の一様な下界。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits
open SerrePositivity.DifferentialGraded
open SerrePositivity.HomologicalAlgebra.CochainProductTotal

namespace SerrePositivity.BhattScholze.Prismatic.HTComparisonTotal

variable {R : Type u} [CommRing R] (K : CochainComplex (Complex R) ℕ)

private structure PrimitivePrefix (q : ℤ) (x : (total K).X q) (n : ℕ) where
  primitive : (total K).X (q-1)
  vanish : ∀ m : ℕ, m < n →
    componentπ K m q (x - (total K).d (q-1) q primitive) = 0
  support : ∀ m : ℕ, n ≤ m → componentπ K m (q-1) primitive = 0

private def zeroPrefix (q : ℤ) (x : (total K).X q) : PrimitivePrefix K q x 0 where
  primitive := 0
  vanish m hm := by omega
  support m _ := map_zero _

private theorem residue_closed (q : ℤ) (x : (total K).X q)
    (hx : (total K).d q (q+1) x = 0) (y : (total K).X (q-1)) :
    (total K).d q (q+1) (x - (total K).d (q-1) q y) = 0 := by
  have hdd := congrArg (fun f => f y) ((total K).d_comp_d (q-1) q (q+1))
  simp only [ModuleCat.comp_apply, ModuleCat.hom_zero, LinearMap.zero_apply] at hdd
  rw [map_sub, hx, hdd, sub_self]

private theorem prefix_step_exists (q : ℤ) (x : (total K).X q)
    (hx : (total K).d q (q+1) x = 0)
    (hd : ∀ n : ℕ, IsZero ((K.X n).homology (q-n)))
    (n : ℕ) (s : PrimitivePrefix K q x n) :
    ∃ t : PrimitivePrefix K q x (n+1),
      ∀ m : ℕ, m < n → componentπ K m (q-1) t.primitive =
        componentπ K m (q-1) s.primitive := by
  obtain ⟨a, _, ha⟩ := kill_first_component K q
    (x - (total K).d (q-1) q s.primitive) (residue_closed K q x hx s.primitive)
    n s.vanish (hd n)
  refine ⟨⟨s.primitive + insert K (q-1) n a, ?_, ?_⟩, ?_⟩
  · intro m hm
    simpa only [map_add, sub_add_eq_sub_sub] using ha m hm
  · intro m hm
    rw [map_add, s.support m (by omega), insert_component_ne K (q-1) n m (by omega)]
    simp
  · intro m hm
    rw [map_add, insert_component_ne K (q-1) n m (by omega), add_zero]

private def nextPrefix (q : ℤ) (x : (total K).X q)
    (hx : (total K).d q (q+1) x = 0)
    (hd : ∀ n : ℕ, IsZero ((K.X n).homology (q-n)))
    (n : ℕ) (s : PrimitivePrefix K q x n) : PrimitivePrefix K q x (n+1) :=
  Classical.choose (prefix_step_exists K q x hx hd n s)

private theorem nextPrefix_stable (q : ℤ) (x : (total K).X q)
    (hx : (total K).d q (q+1) x = 0)
    (hd : ∀ n : ℕ, IsZero ((K.X n).homology (q-n)))
    (n : ℕ) (s : PrimitivePrefix K q x n) (m : ℕ) (hm : m < n) :
    componentπ K m (q-1) (nextPrefix K q x hx hd n s).primitive =
      componentπ K m (q-1) s.primitive :=
  Classical.choose_spec (prefix_step_exists K q x hx hd n s) m hm

private def prefixes (q : ℤ) (x : (total K).X q)
    (hx : (total K).d q (q+1) x = 0)
    (hd : ∀ n : ℕ, IsZero ((K.X n).homology (q-n))) :
    (n : ℕ) → PrimitivePrefix K q x n :=
  Nat.rec (zeroPrefix K q x) (fun n s => nextPrefix K q x hx hd n s)

private theorem prefix_component_stable (q : ℤ) (x : (total K).X q)
    (hx : (total K).d q (q+1) x = 0)
    (hd : ∀ n : ℕ, IsZero ((K.X n).homology (q-n)))
    (m n : ℕ) (h : m+1 ≤ n) :
    componentπ K m (q-1) (prefixes K q x hx hd n).primitive =
      componentπ K m (q-1) (prefixes K q x hx hd (m+1)).primitive := by
  revert h
  induction n with
  | zero => intro h; omega
  | succ n ih =>
    intro h
    by_cases heq : n = m
    · subst n
      rfl
    · have hn : m+1 ≤ n := by omega
      change componentπ K m (q-1)
        (nextPrefix K q x hx hd n (prefixes K q x hx hd n)).primitive = _
      rw [nextPrefix_stable K q x hx hd n (prefixes K q x hx hd n) m (by omega)]
      exact ih hn

private def finalPrimitive (q : ℤ) (x : (total K).X q)
    (hx : (total K).d q (q+1) x = 0)
    (hd : ∀ n : ℕ, IsZero ((K.X n).homology (q-n))) : (total K).X (q-1) :=
  (componentsLinearEquiv K (q-1)).symm
    (fun n => componentπ K n (q-1) (prefixes K q x hx hd (n+1)).primitive)

private theorem finalPrimitive_component (q : ℤ) (x : (total K).X q)
    (hx : (total K).d q (q+1) x = 0)
    (hd : ∀ n : ℕ, IsZero ((K.X n).homology (q-n))) (m : ℕ) :
    componentπ K m (q-1) (finalPrimitive K q x hx hd) =
      componentπ K m (q-1) (prefixes K q x hx hd (m+1)).primitive := by
  change (componentsLinearEquiv K (q-1)
    ((componentsLinearEquiv K (q-1)).symm _)) m = _
  rw [LinearEquiv.apply_symm_apply]

/-- 対角線の各行が完全なら、全余輪体に同じ積全複体内の原始元がある。 -/
theorem exists_total_primitive (q : ℤ) (x : (total K).X q)
    (hx : (total K).d q (q+1) x = 0)
    (hd : ∀ n : ℕ, IsZero ((K.X n).homology (q-n))) :
    ∃ y : (total K).X (q-1), (total K).d (q-1) q y = x := by
  refine ⟨finalPrimitive K q x hx hd, ?_⟩
  apply ext K
  intro n
  have hh : componentπ K n q ((total K).d (q-1) q (finalPrimitive K q x hx hd)) =
      componentπ K n q ((total K).d (q-1) q (prefixes K q x hx hd (n+1)).primitive) := by
    have h := differential_component_congr K (q-1) n (finalPrimitive K q x hx hd)
      (prefixes K q x hx hd (n+1)).primitive (by
        intro m hm
        rw [finalPrimitive_component]
        exact (prefix_component_stable K q x hx hd m (n+1) (by omega)).symm)
    have hq : q - 1 + 1 = q := by omega
    rw [hq] at h
    exact h
  have hz := (prefixes K q x hx hd (n+1)).vanish n (by omega)
  rw [map_sub] at hz
  exact hh.trans (sub_eq_zero.mp hz).symm

/-- 指定対角線の行ホモロジーの零性から、積全複体の同じ次数の零性が従う。 -/
theorem total_homology_isZero_of_diagonal (q : ℤ)
    (hd : ∀ n : ℕ, IsZero ((K.X n).homology (q-n))) :
    IsZero ((total K).homology q) := by
  apply (HomologicalComplex.exactAt_iff_isZero_homology (total K) q).mp
  apply ((total K).exactAt_iff' (q-1) q (q+1) (by simp) (by simp)).mpr
  apply (ShortComplex.moduleCat_exact_iff _).mpr
  intro x hx
  exact exists_total_primitive K q x hx hd

/-- 各行の一様なコホモロジーの下界は、積全複体の同じ下界を与える。 -/
theorem total_lowerBound (b : ℤ)
    (h : ∀ n : ℕ, ∀ i : ℤ, i < b → IsZero ((K.X n).homology i))
    (q : ℤ) (hq : q < b) : IsZero ((total K).homology q) :=
  total_homology_isZero_of_diagonal K q (fun n => h n (q-n) (by omega))

/-- 行ごとに異なる下界も、横次数を足した共通の下界として全複体へ渡る。 -/
theorem total_lowerBound_of_rowBounds (b : ℕ → ℤ) (c : ℤ)
    (h : ∀ n : ℕ, ∀ i : ℤ, i < b n → IsZero ((K.X n).homology i))
    (hc : ∀ n : ℕ, c ≤ (n : ℤ) + b n) (q : ℤ) (hq : q < c) :
    IsZero ((total K).homology q) :=
  total_homology_isZero_of_diagonal K q (fun n => h n (q-n) (by have := hc n; omega))

end SerrePositivity.BhattScholze.Prismatic.HTComparisonTotal
