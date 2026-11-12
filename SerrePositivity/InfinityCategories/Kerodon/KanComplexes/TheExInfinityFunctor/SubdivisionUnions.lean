module

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.SubdivisionDegeneracy
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.FiniteChainUnion

/-!
# 細分作用素の和集合保存

概要：複雑度を切る作用素と拡張退化が非空有限集合の和を保つことを示す。
方針：各作用素の像に頂点が属する条件を存在量化で書き、和集合と交換する。
規約：Moss 2020 Lemma 26 の singleton 上の計算への帰着。
使われ方：面・退化との交換則の証明。

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
概要：複雑度を切った有限鎖の頂点を、元の頂点からの条件で特徴付ける。
方針：閾値を超える頂点があれば、その頂点以下が追加される。
規約：Moss 2020 Definition 23 の binary join による式。
使われ方：複雑度作用素の和集合保存。
-/
theorem finiteChainCut_mem_iff (n : ℕ) (k x : ULift.{u} (Fin (n + 1)))
    (s : NonemptyFiniteChains (ULift.{u} (Fin (n + 1)))) :
    x ∈ (finiteChainCut n k s).finset ↔
      x ∈ s.finset ∨ ∃ a ∈ s.finset, k < a ∧ x ≤ a := by
  change x ∈ (if finiteChainMaximum s ≤ k then s else
    finiteChainInitialSegment n (finiteChainMaximum s)).finset ↔ _
  by_cases hm : finiteChainMaximum s ≤ k
  · rw [ite_eq_left hm]
    constructor
    · exact Or.inl
    · rintro (hx | ⟨a, ha, hka, _⟩)
      · exact hx
      · exact (not_lt_of_ge ((Finset.le_max' s.finset a ha).trans hm) hka).elim
  · rw [ite_eq_right hm]
    change x ∈ (Finset.univ.filter (fun i => i ≤ finiteChainMaximum s)) ↔ _
    rw [Finset.mem_filter]
    constructor
    · intro hx
      exact Or.inr ⟨finiteChainMaximum s, Finset.max'_mem s.finset s.nonempty,
        lt_of_not_ge hm, hx.2⟩
    · rintro (hx | ⟨a, ha, _, hxa⟩)
      · exact ⟨Finset.mem_univ _, Finset.le_max' s.finset x hx⟩
      · exact ⟨Finset.mem_univ _, hxa.trans (Finset.le_max' s.finset a ha)⟩

/--
概要：複雑度を切る作用素は非空有限鎖の和を保つ。
方針：頂点の所属条件の存在量化と和集合を交換する。
規約：Moss 2020 Lemma 26 の singleton 上の比較の前提。
使われ方：j_n^k を含む合成写像の比較。
-/
theorem finiteChainCut_preservesUnion (n : ℕ) (k : ULift.{u} (Fin (n + 1))) :
    PreservesFiniteChainUnion (finiteChainCut n k) := by
  intro a b
  apply NonemptyFiniteChains.ext
  ext x
  simp only [finiteChainCut_mem_iff, finiteChainUnion, finiteChainOfFinset, Finset.mem_union]
  aesop

/--
概要：拡張退化で得られる頂点の所属条件。
方針：通常の退化による像と、指定頂点を含むとき追加する初期区間に分ける。
規約：Moss 2020 Definition 25 の binary join による式。
使われ方：拡張退化の和集合保存。
-/
theorem finiteChainDegeneracy_mem_iff (n : ℕ) (k : Fin (n + 1))
    (s : NonemptyFiniteChains (ULift.{u} (Fin (n + 2)))) (x : ULift.{u} (Fin (n + 1))) :
    x ∈ (finiteChainDegeneracy n k s).finset ↔
      (∃ a ∈ s.finset, liftedDegeneracy n k a = x) ∨
        (ULift.up k.succ ∈ s.finset ∧ x ≤ ULift.up k) := by
  by_cases h : ULift.up k.succ ∈ s.finset
  · simp only [finiteChainDegeneracy, OrderHom.coe_mk, h, ↓reduceIte, Finset.mem_union,
      NonemptyFiniteChains.mem_map_iff, finiteChainInitialSegment, Finset.mem_filter,
      Finset.mem_univ, true_and]
  · simp only [finiteChainDegeneracy, OrderHom.coe_mk, h, ↓reduceIte,
      NonemptyFiniteChains.mem_map_iff, false_and, or_false]

/--
概要：拡張退化は非空有限鎖の和を保つ。
方針：頂点の所属条件の存在量化を和集合へ分配する。
規約：Moss 2020 Lemma 26 の r_n^k を含む比較の前提。
使われ方：面・退化との九つの交換則。
-/
theorem finiteChainDegeneracy_preservesUnion (n : ℕ) (k : Fin (n + 1)) :
    PreservesFiniteChainUnion (finiteChainDegeneracy.{u} n k) := by
  intro a b
  apply NonemptyFiniteChains.ext
  ext x
  simp only [finiteChainDegeneracy_mem_iff, finiteChainUnion, finiteChainOfFinset, Finset.mem_union]
  aesop

end SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor
