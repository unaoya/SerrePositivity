module

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.SubdivisionLastVertex
public import Mathlib.Order.Preorder.Finite
public import Mathlib.Tactic.CrossRefAttribute

/-!
# 部分順序集合の非空有限鎖の最大元

概要：部分順序集合の非空有限鎖には最大元があり、包含に関して単調である。
方針：有限集合の極大元と、鎖の全ての二元の比較可能性を組み合わせる。
規約：Moss 2020 Proposition 21 の二重細分の有限鎖の計算に用いる補助。
使われ方：線形順序を仮定せず反復細分の最終頂点を計算する。

対応節は Kerodon 3.3（Tag 00XF）。
-/

@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor
open PartialOrder

/--
概要：非空有限鎖には最大元が存在する。
方針：有限集合の極大元が鎖では全ての元の上界になることを使う。
規約：部分順序だけを仮定する。
使われ方：有限鎖から最大元を選ぶ写像。
-/
theorem finiteChain_exists_greatest {P : Type u} [PartialOrder P] (s : NonemptyFiniteChains P) :
    ∃ a, a ∈ s.finset ∧ ∀ b ∈ s.finset, b ≤ a := by
  obtain ⟨a, ha, hm⟩ := s.finset.exists_maximal s.nonempty
  refine ⟨a, ha, ?_⟩
  intro b hb
  rcases s.comparable ⟨b, hb⟩ ⟨a, ha⟩ with h | h
  · exact h
  · exact hm hb h

/--
概要：部分順序集合の非空有限鎖を最大元へ送る単調写像。
方針：最大元の存在から選び、その上界の性質で包含に関する単調性を示す。
規約：線形順序上の finiteChainMaximum を部分順序へ拡張する補助。
使われ方：反復された有限鎖の最終頂点。
-/
@[kerodon 00YS]
def finiteChainGreatest {P : Type u} [PartialOrder P] : NonemptyFiniteChains P →o P where
  toFun s := (finiteChain_exists_greatest s).choose
  monotone' s t h := (finiteChain_exists_greatest t).choose_spec.2 _
    (h (finiteChain_exists_greatest s).choose_spec.1)

/--
概要：選んだ最大元は元の鎖に属する。
方針：最大元の存在の証明の所属条件を取る。
規約：部分順序の有限鎖の最大元。
使われ方：最大元を像や上界の議論に使う。
-/
theorem finiteChainGreatest_mem {P : Type u} [PartialOrder P] (s : NonemptyFiniteChains P) :
    finiteChainGreatest s ∈ s.finset := (finiteChain_exists_greatest s).choose_spec.1

/--
概要：鎖の全ての元は選んだ最大元以下である。
方針：最大元の存在の証明の上界条件を使う。
規約：部分順序の有限鎖の最大元。
使われ方：最大元の関手性。
-/
theorem le_finiteChainGreatest {P : Type u} [PartialOrder P] (s : NonemptyFiniteChains P)
    (a : P) (ha : a ∈ s.finset) : a ≤ finiteChainGreatest s :=
  (finiteChain_exists_greatest s).choose_spec.2 a ha

/--
概要：部分順序集合でも最大元は単調写像の像と可換である。
方針：像の全ての元の上界と、元の最大元自身の像への所属を使う。
規約：反復細分で用いる最終頂点の自然性。
使われ方：細分比較と反復最終頂点の一致。
-/
theorem finiteChainGreatest_map {P Q : Type u} [PartialOrder P] [PartialOrder Q]
    (f : P →o Q) (s : NonemptyFiniteChains P) :
    finiteChainGreatest (s.map f) = f (finiteChainGreatest s) := by
  apply le_antisymm
  · obtain ⟨a, ha, he⟩ := (NonemptyFiniteChains.mem_map_iff s f _).mp
      (finiteChainGreatest_mem (s.map f))
    rw [← he]
    exact f.monotone (le_finiteChainGreatest s a ha)
  · exact le_finiteChainGreatest (s.map f) _ ((NonemptyFiniteChains.mem_map_iff s f _).mpr
      ⟨_, finiteChainGreatest_mem s, rfl⟩)

/--
概要：線形順序の場合、部分順序の最大元と有限集合の最大元は一致する。
方針：双方が同じ非空有限集合の最大元であることから反対称性を使う。
規約：既存の最終頂点との計算上の整合。
使われ方：標準単体の細分比較と最終頂点を合わせる。
-/
theorem finiteChainGreatest_eq_maximum {P : Type u} [LinearOrder P]
    (s : NonemptyFiniteChains P) : finiteChainGreatest s = finiteChainMaximum s := by
  apply le_antisymm
  · exact Finset.le_max' s.finset _ (finiteChainGreatest_mem s)
  · exact le_finiteChainGreatest s _ (Finset.max'_mem s.finset s.nonempty)

end SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor
