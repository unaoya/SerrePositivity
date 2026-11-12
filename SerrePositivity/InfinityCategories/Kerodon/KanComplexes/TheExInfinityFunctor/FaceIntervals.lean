module

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.SubdivisionIntervals

/-!
# 面写像の初期区間上の計算

概要：削除する頂点より前の初期区間は、面写像の像でも同じ初期区間になる。
方針：面写像の単射性と、除いた頂点以外の逆像を使う。
規約：Moss 2020 Lemma 26 (3) の生成元上の計算。
使われ方：後ろの面と拡張退化の交換則。

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
概要：ULift した面写像は単射である。
方針：Fin.succAbove の狭義単調性を使う。
規約：Moss 2020 Lemma 26 (3) の特別な頂点の逆像。
使われ方：指定頂点以外が特別な頂点へ入らないこと。
-/
theorem liftedFace_injective (n : ℕ) (i : Fin (n + 2)) :
    Function.Injective (liftedFace.{u} n i) := by
  intro a b h
  apply ULift.ext
  exact (Fin.strictMono_succAbove i).injective (congrArg ULift.down h)

/--
概要：削除する頂点より前の頂点は castSucc による同じ番号の頂点へ送られる。
方針：Fin.succAbove の削除頂点より小さい場合の式を使う。
規約：Moss 2020 Lemma 26 (3) の面の計算。
使われ方：初期区間の像の右端の計算。
-/
theorem liftedFace_of_below (n : ℕ) (i : Fin (n + 2)) (k : Fin (n + 1)) (h : k.castSucc < i) :
    liftedFace.{u} n i (ULift.up k) = ULift.up k.castSucc := by
  apply ULift.ext
  exact Fin.succAbove_of_castSucc_lt i k h

/--
概要：面写像は削除する頂点より前の初期区間を同じ番号の初期区間へ送る。
方針：像の各頂点は変わらず、像側の頂点は削除頂点を避けるので逆像を持つ。
規約：Moss 2020 Lemma 26 (3) の r_n^k の初期区間の整合。
使われ方：面と拡張退化の交換則。
-/
theorem liftedFace_initialSegment_of_below (n : ℕ) (i : Fin (n + 2)) (k : Fin (n + 1))
    (hki : k.castSucc < i) :
    (finiteChainInitialSegment n (ULift.up k)).map (liftedFace.{u} n i) =
      finiteChainInitialSegment (n + 1) (ULift.up k.castSucc) := by
  apply NonemptyFiniteChains.ext
  ext x
  rw [NonemptyFiniteChains.mem_map_iff]
  constructor
  · rintro ⟨j, hj, rfl⟩
    have hjk : j.down ≤ k := (Finset.mem_filter.mp hj).2
    have hji : j.down.castSucc < i := (Fin.castSucc_le_castSucc_iff.mpr hjk).trans_lt hki
    have hf : liftedFace n i j = ULift.up j.down.castSucc :=
      liftedFace_of_below n i j.down hji
    rw [hf]
    change ULift.up j.down.castSucc ∈ Finset.univ.filter (fun a => a ≤ ULift.up k.castSucc)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact Fin.castSucc_le_castSucc_iff.mpr hjk
  · intro hx
    have hxk : x.down ≤ k.castSucc := (Finset.mem_filter.mp hx).2
    obtain ⟨j, hj⟩ := Fin.exists_succAbove_eq (hxk.trans_lt hki).ne
    have hjk : j ≤ k := by
      apply (Fin.succAbove_le_succAbove_iff (p := i)).mp
      rw [hj, Fin.succAbove_of_castSucc_lt i k hki]
      exact hxk
    refine ⟨ULift.up j, by simp [finiteChainInitialSegment, hjk], ?_⟩
    exact ULift.ext hj

end SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor
