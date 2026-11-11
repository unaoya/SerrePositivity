module

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.FiniteChainGreatest

/-!
# 二重細分の horn に向かう頂点写像

概要：非空な面の有限鎖から、horn 内の単体を張る頂点を単調に選ぶ。
方針：horn に属する面では最大頂点、それ以外では欠けた面の添字を取り、その像の最大元を取る。
規約：Moss 2020 Proposition 21 の Kan 性に向けた二重細分の直接的な計算。
使われ方：二重細分から horn への充填写像の頂点の構成。

対応節は Kerodon 3.3（Tag 00XF）。
-/

@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor
open PartialOrder

/--
概要：面が k-horn に属するための頂点集合上の条件。
方針：k と異なる頂点が少なくとも一つ欠けていることを要求する。
規約：通常の horn は k 番目以外の全ての余次元一の面の和である。
使われ方：二重細分の有限鎖における面の分類。
-/
def HornFaceSet (n : ℕ) (k : Fin (n + 1))
    (s : NonemptyFiniteChains (ULift.{u} (Fin (n + 1)))) : Prop :=
  ∃ j : Fin (n + 1), j ≠ k ∧ ULift.up j ∉ s.finset

/--
概要：horn に属する面の部分面も horn に属する。
方針：大きい面に欠けている頂点は小さい面にも欠けている。
規約：horn の部分複体の性質を頂点集合で表す。
使われ方：horn の細分に含まれる有限鎖の判定。
-/
theorem hornFaceSet_of_le (n : ℕ) (k : Fin (n + 1))
    (s t : NonemptyFiniteChains (ULift.{u} (Fin (n + 1)))) (hst : s ≤ t)
    (ht : HornFaceSet n k t) : HornFaceSet n k s := by
  obtain ⟨j, hj, hm⟩ := ht
  exact ⟨j, hj, fun h => hm (hst h)⟩

/--
概要：horn に属する面の最大頂点を取り、属さない面では k を取る。
方針：horn の面の条件で場合分けする。
規約：この写像自体の単調性は要求しない。
使われ方：有限鎖全体の像の最大元を取って単調写像を作る。
-/
def hornFaceChoice (n : ℕ) (k : Fin (n + 1))
    (s : NonemptyFiniteChains (ULift.{u} (Fin (n + 1)))) : ULift.{u} (Fin (n + 1)) := by
  classical
  exact if HornFaceSet n k s then finiteChainMaximum s else ULift.up k

/--
概要：面の有限鎖を、選んだ頂点たちの最大元へ送る単調写像。
方針：非空有限集合の像の最大元を取り、包含に対する最大元の単調性を使う。
規約：二重細分の頂点に対する horn への候補写像。
使われ方：順序集合の nerve から horn に向かう写像。
-/
def hornChainVertex (n : ℕ) (k : Fin (n + 1)) :
    NonemptyFiniteChains (NonemptyFiniteChains (ULift.{u} (Fin (n + 1)))) →o
      ULift.{u} (Fin (n + 1)) := by
  classical
  exact
    { toFun C := (C.finset.image (hornFaceChoice n k)).max' (C.nonempty.image _)
      monotone' C D h := Finset.max'_subset (C.nonempty.image _) ((Finset.image_mono _) h) }

/--
概要：有限鎖から選んだ頂点は、その鎖のある面から選んだ頂点に等しい。
方針：有限集合の像の最大元の所属を使う。
規約：二重細分の頂点写像の具体的な表示。
使われ方：候補の像が一つの horn の面に入ること。
-/
theorem hornChainVertex_exists_face (n : ℕ) (k : Fin (n + 1))
    (C : NonemptyFiniteChains (NonemptyFiniteChains (ULift.{u} (Fin (n + 1))))) :
    ∃ s ∈ C.finset, hornFaceChoice n k s = hornChainVertex n k C := by
  classical
  exact Finset.mem_image.mp (Finset.max'_mem (C.finset.image (hornFaceChoice n k))
    (C.nonempty.image _))

/--
概要：鎖の全ての面が horn 内にある場合、候補頂点は通常の反復最大元である。
方針：最大の面自身の像による下界と、他の全ての面の像の上界を使う。
規約：horn 上での反復最終頂点との一致の頂点上の式。
使われ方：二重細分の充填の境界条件。
-/
theorem hornChainVertex_of_all_faces (n : ℕ) (k : Fin (n + 1))
    (C : NonemptyFiniteChains (NonemptyFiniteChains (ULift.{u} (Fin (n + 1)))))
    (hC : ∀ s ∈ C.finset, HornFaceSet n k s) :
    hornChainVertex n k C = finiteChainMaximum (finiteChainGreatest C) := by
  classical
  apply le_antisymm
  · obtain ⟨s, hs, he⟩ := hornChainVertex_exists_face n k C
    rw [← he]
    change (if HornFaceSet n k s then _ else _) ≤ _
    rw [ite_eq_left (hC s hs)]
    exact finiteChainMaximum.monotone (le_finiteChainGreatest C s hs)
  · have hm : hornFaceChoice n k (finiteChainGreatest C) ≤ hornChainVertex n k C :=
      Finset.le_max' (C.finset.image (hornFaceChoice n k)) _
        (Finset.mem_image.mpr ⟨_, finiteChainGreatest_mem C, rfl⟩)
    change (if HornFaceSet n k (finiteChainGreatest C) then _ else _) ≤ _ at hm
    rw [ite_eq_left (hC _ (finiteChainGreatest_mem C))] at hm
    exact hm

end SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor
