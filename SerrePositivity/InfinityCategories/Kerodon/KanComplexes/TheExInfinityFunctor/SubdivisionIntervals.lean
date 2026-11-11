module

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.SubdivisionUnions
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.FiniteChainIntervals

/-!
# 細分作用素の初期区間上の式

概要：複雑度作用素と拡張退化の singleton・初期区間上の式を計算する。
方針：最大元の計算と単調な全射の初期区間の像を使う。
規約：Moss 2020 Lemma 26 の交換則の生成元上の検証。
使われ方：和集合を保つ作用素の比較原理へ渡す。

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
概要：初期区間は全ての複雑度作用素で固定される。
方針：最大元はその区間の右端であり、再び初期区間を取っても変わらない。
規約：Moss 2020 Lemma 26 の j_n^k の計算。
使われ方：作用素の交換則の初期区間に入る場合。
-/
theorem finiteChainCut_initialSegment (n : ℕ) (k i : ULift.{u} (Fin (n + 1))) :
    finiteChainCut n k (finiteChainInitialSegment n i) = finiteChainInitialSegment n i := by
  change (if finiteChainMaximum (finiteChainInitialSegment n i) ≤ k then _ else _) = _
  rw [finiteChainMaximum_initialSegment]
  split_ifs <;> rfl

/--
概要：複雑度作用素の singleton 上の式。
方針：singleton の最大元を評価する。
規約：Moss 2020 Definition 23 の原典の singleton 上の定義との一致。
使われ方：和を保つ写像の生成元上の比較。
-/
theorem finiteChainCut_singleton (n : ℕ) (k i : ULift.{u} (Fin (n + 1))) :
    finiteChainCut n k (finiteChainSingleton i) =
      if i ≤ k then finiteChainSingleton i else finiteChainInitialSegment n i := by
  change (if finiteChainMaximum (finiteChainSingleton i) ≤ k then _ else _) = _
  rw [finiteChainMaximum_singleton]

/--
概要：通常の退化は二つ目の指定頂点 k+1 を k に送る。
方針：Fin の predAbove の同じ添字での式を使う。
規約：Moss 2020 Definition 25 の特別な頂点。
使われ方：拡張退化で加える初期区間の右端。
-/
theorem liftedDegeneracy_succ (n : ℕ) (k : Fin (n + 1)) :
    liftedDegeneracy.{u} n k (ULift.up k.succ) = ULift.up k := by
  apply ULift.ext
  exact Fin.predAbove_succ_self k

/--
概要：通常の退化は頂点上で全射である。
方針：指定した余面との合成が恒等であることを使う。
規約：Moss 2020 Lemma 26 (1) の通常の退化部分。
使われ方：初期区間の像の公式。
-/
theorem liftedDegeneracy_surjective (n : ℕ) (k : Fin (n + 1)) :
    Function.Surjective (liftedDegeneracy.{u} n k) := by
  intro x
  refine ⟨liftedFace n k.succ x, ?_⟩
  apply ULift.ext
  exact congrArg (fun f : SimplexCategory.mk n ⟶ SimplexCategory.mk n => f x.down)
    SimplexCategory.δ_comp_σ_succ

/--
概要：拡張退化は初期区間を、通常の退化の像の頂点までの初期区間に送る。
方針：通常の退化の全射性で像を計算し、追加する区間が既存の像に含まれることを示す。
規約：Moss 2020 Lemma 26 の r_n^k の生成元上の計算。
使われ方：複雑度作用素との交換則。
-/
theorem finiteChainDegeneracy_initialSegment (n : ℕ) (k : Fin (n + 1))
    (i : ULift.{u} (Fin (n + 2))) :
    finiteChainDegeneracy n k (finiteChainInitialSegment (n + 1) i) =
      finiteChainInitialSegment n (liftedDegeneracy n k i) := by
  let s := finiteChainInitialSegment (n + 1) i
  have hmap : s.map (liftedDegeneracy n k) =
      finiteChainInitialSegment n (liftedDegeneracy n k i) :=
    finiteChainInitialSegment_map _ (liftedDegeneracy_surjective n k) i
  change (if ULift.up k.succ ∈ s.finset then _ else _) = _
  by_cases hs : ULift.up k.succ ∈ s.finset
  · rw [ite_eq_left hs]
    apply NonemptyFiniteChains.ext
    change (s.map (liftedDegeneracy n k)).finset ∪
      (finiteChainInitialSegment n (ULift.up k)).finset = _
    rw [hmap]
    apply Finset.union_eq_left.mpr
    have hki : ULift.up k.succ ≤ i := (Finset.mem_filter.mp hs).2
    have hk : ULift.up k ≤ liftedDegeneracy n k i := by
      rw [← liftedDegeneracy_succ n k]
      exact (liftedDegeneracy n k).monotone hki
    exact (finiteChainInitialSegment n).monotone hk
  · rw [ite_eq_right hs]
    exact hmap

/--
概要：拡張退化の singleton 上の式。
方針：特別な頂点では初期区間を取り、それ以外では通常の退化の像を取る。
規約：Moss 2020 Definition 25 の原典の生成元上の定義との一致。
使われ方：和を保つ写像の比較原理。
-/
theorem finiteChainDegeneracy_singleton (n : ℕ) (k : Fin (n + 1))
    (i : ULift.{u} (Fin (n + 2))) :
    finiteChainDegeneracy n k (finiteChainSingleton i) =
      if i = ULift.up k.succ then finiteChainInitialSegment n (ULift.up k)
      else finiteChainSingleton (liftedDegeneracy n k i) := by
  by_cases h : i = ULift.up k.succ
  · rw [ite_eq_left h]
    subst i
    apply NonemptyFiniteChains.ext
    ext x
    simp only [finiteChainDegeneracy_mem_iff, finiteChainSingleton, finiteChainOfFinset,
      Finset.mem_singleton, exists_eq_left, liftedDegeneracy_succ,
      finiteChainInitialSegment, OrderHom.coe_mk, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro (hx | hx)
      · exact le_of_eq hx.symm
      · exact hx
    · exact Or.inr
  · rw [ite_eq_right h]
    apply NonemptyFiniteChains.ext
    ext x
    simp [finiteChainDegeneracy_mem_iff, finiteChainSingleton, finiteChainOfFinset, Ne.symm h,
      eq_comm]

end SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor
