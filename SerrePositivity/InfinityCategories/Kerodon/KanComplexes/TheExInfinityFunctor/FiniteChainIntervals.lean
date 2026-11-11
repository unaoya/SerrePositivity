module

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.FiniteChainUnion

/-!
# 非空有限鎖の初期区間と単調な全射

概要：singleton の最大元と初期区間の像を計算する。
方針：全射の逆像を選び、必要なら区間の右端の頂点へ移す。
規約：Moss 2020 Lemma 26 の細分作用素の計算の補助。
使われ方：通常の退化と拡張退化の初期区間上の式。

対応節は Kerodon 3.3（Tag 00XF）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
namespace SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor
open CategoryTheory PartialOrder

/--
概要：singleton の最大元はその頂点である。
方針：有限集合の最大元の計算を使う。
規約：Moss 2020 Lemma 26 の生成元上の計算。
使われ方：複雑度作用素の singleton 上の式。
-/
theorem finiteChainMaximum_singleton {α : Type u} [LinearOrder α] (a : α) :
    finiteChainMaximum (finiteChainSingleton a) = a := by
  simp [finiteChainMaximum, finiteChainSingleton, finiteChainOfFinset]

/--
概要：単調写像による singleton の像は像の頂点の singleton である。
方針：像の所属条件を計算する。
規約：Moss 2020 Lemma 26 の生成元の像。
使われ方：面・退化の細分の singleton 上の式。
-/
theorem finiteChainMap_singleton {α β : Type u} [LinearOrder α] [LinearOrder β]
    (f : α →o β) (a : α) : (finiteChainSingleton a).map f = finiteChainSingleton (f a) := by
  apply NonemptyFiniteChains.ext
  ext x
  simp [NonemptyFiniteChains.mem_map_iff, finiteChainSingleton, finiteChainOfFinset, eq_comm]

/--
概要：初期区間同士の包含は右端の頂点の大小に等しい。
方針：右端の頂点自身を評価し、逆向きは初期区間の単調性を使う。
規約：Moss 2020 Lemma 26 の初期区間の計算。
使われ方：拡張退化で加える区間が既存の像に含まれること。
-/
theorem finiteChainInitialSegment_le_iff (n : ℕ) (i j : ULift.{u} (Fin (n + 1))) :
    finiteChainInitialSegment n i ≤ finiteChainInitialSegment n j ↔ i ≤ j := by
  constructor
  · intro h
    have hi : i ∈ (finiteChainInitialSegment n i).finset := by simp [finiteChainInitialSegment]
    exact (Finset.mem_filter.mp (h hi)).2
  · intro h
    exact (finiteChainInitialSegment n).monotone h

/--
概要：単調な全射は初期区間を像の右端の初期区間へ送る。
方針：逆像が右端より大きいときは、単調性から右端自身も同じ像になる。
規約：Moss 2020 Lemma 26 の通常の退化の像の計算。
使われ方：拡張退化と初期区間の交換。
-/
theorem finiteChainInitialSegment_map {n m : ℕ}
    (f : ULift.{u} (Fin (n + 1)) →o ULift.{u} (Fin (m + 1))) (hf : Function.Surjective f)
    (i : ULift.{u} (Fin (n + 1))) :
    (finiteChainInitialSegment n i).map f = finiteChainInitialSegment m (f i) := by
  apply NonemptyFiniteChains.ext
  ext x
  rw [NonemptyFiniteChains.mem_map_iff]
  constructor
  · rintro ⟨j, hj, rfl⟩
    change f j ∈ Finset.univ.filter (fun k => k ≤ f i)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact f.monotone (Finset.mem_filter.mp hj).2
  · intro hx
    have hx' : x ≤ f i := (Finset.mem_filter.mp hx).2
    obtain ⟨j, hj⟩ := hf x
    by_cases hji : j ≤ i
    · exact ⟨j, by simp [finiteChainInitialSegment, hji], hj⟩
    · refine ⟨i, by simp [finiteChainInitialSegment], ?_⟩
      exact le_antisymm (by rw [← hj]; exact f.monotone (le_of_not_ge hji)) hx'

end SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor
