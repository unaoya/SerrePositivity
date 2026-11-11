module

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.SubdivisionIntervals

/-!
# 拡張退化の最大元の計算

概要：拡張退化の最大元は通常の退化で最大元を送ったものに等しい。
方針：追加する初期区間の右端は、既にある通常の退化の像以下である。
規約：Moss 2020 Lemma 26 (2) の最大元を用いる補助証明。
使われ方：前側の面の作用素が初期区間へ入ること。

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
概要：拡張退化は最大元の通常の退化による像を最大元に持つ。
方針：像の所属条件で最大元の上界と、その上界自身の所属を示す。
規約：Moss 2020 Lemma 26 (2) の補助。
使われ方：前側の面の複雑度の上界。
-/
theorem finiteChainDegeneracy_maximum (n : ℕ) (k : Fin (n + 1))
    (s : NonemptyFiniteChains (ULift.{u} (Fin (n + 2)))) :
    finiteChainMaximum (finiteChainDegeneracy n k s) =
      liftedDegeneracy n k (finiteChainMaximum s) := by
  apply le_antisymm
  · apply Finset.max'_le _ (finiteChainDegeneracy n k s).nonempty
    intro x hx
    rcases (finiteChainDegeneracy_mem_iff n k s x).mp hx with ⟨a, ha, rfl⟩ | ⟨hs, hx⟩
    · exact (liftedDegeneracy n k).monotone (Finset.le_max' s.finset a ha)
    · have hk : ULift.up k ≤ liftedDegeneracy n k (finiteChainMaximum s) := by
        rw [← liftedDegeneracy_succ n k]
        exact (liftedDegeneracy n k).monotone (Finset.le_max' s.finset _ hs)
      exact hx.trans hk
  · exact Finset.le_max' _ _ ((finiteChainDegeneracy_mem_iff n k s _).mpr
      (Or.inl ⟨finiteChainMaximum s, Finset.max'_mem s.finset s.nonempty, rfl⟩))

/--
概要：指定頂点以上の頂点を前側の面と通常の退化で送ると元へ戻る。
方針：面は一つ上げ、退化はその一つを下げる。
規約：Moss 2020 Lemma 26 (2) の最大元の計算。
使われ方：前側の面の作用素の最大元の保存。
-/
theorem liftedDegeneracy_face_ge (n : ℕ) (k : Fin (n + 1)) (i : Fin (n + 2))
    (hi : i ≤ k.castSucc) (x : ULift.{u} (Fin (n + 1))) (hx : ULift.up k ≤ x) :
    liftedDegeneracy n k (liftedFace n i x) = x := by
  apply ULift.ext
  change k.predAbove (i.succAbove x.down) = x.down
  rw [Fin.succAbove_of_le_castSucc i x.down (hi.trans (Fin.castSucc_le_castSucc_iff.mpr hx))]
  exact Fin.predAbove_succ_of_le k x.down hx

end SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor
