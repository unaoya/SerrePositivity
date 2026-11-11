module

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.OrderNerveSubcomplexIso
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.HornFacePoset
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.FiniteChainUnion

/-!
# horn の面の順序集合の包含の anodyne 性

概要：horn に属する面の順序集合の nerve の包含は anodyne である。
方針：欠けた面の添字 k を頂点集合へ加え、恒等写像と singleton {k} から比較する。
規約：Moss arXiv:1506.04887v2 Proposition 2.19 に現れる面の模型。
この段階では実際の細分された horn との同型は主張しない。
使われ方：細分比較が同型であることを示した後の anodyne 性の移送。

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
概要：非空の面に指定した頂点を加える単調写像。
方針：有限集合の insert を使い、包含を保つことを確認する。
規約：全頂点が線形順序なので insert した集合も面の有限鎖を表す。
使われ方：horn の面の包含の収縮の共通の上側の写像。
-/
def hornFaceAddVertex (n : ℕ) (k : Fin (n + 1)) :
    NonemptyFiniteChains (ULift.{u} (Fin (n + 1))) →o
      NonemptyFiniteChains (ULift.{u} (Fin (n + 1))) where
  toFun s := finiteChainOfFinset (insert (ULift.up k) s.finset) (Finset.insert_nonempty _ _)
  monotone' _ _ h := Finset.insert_subset_insert _ h

/--
概要：k-horn に属する面に頂点 k を加えても、その面は k-horn に属する。
方針：k と異なる欠けた頂点は insert の後も欠けている。
規約：原典の安全な面の集合の不変性。
使われ方：面の nerve の部分対象を保つ収縮。
-/
theorem hornFaceAddVertex_mem (n : ℕ) (k : Fin (n + 1))
    (s : NonemptyFiniteChains (ULift.{u} (Fin (n + 1)))) (hs : HornFaceSet n k s) :
    HornFaceSet n k (hornFaceAddVertex n k s) := by
  obtain ⟨j, hj, hm⟩ := hs
  refine ⟨j, hj, ?_⟩
  change ULift.up j ∉ insert (ULift.up k) s.finset
  simpa only [Finset.mem_insert, ULift.up.injEq, hj, false_or] using hm

/--
概要：正次元の k-horn は singleton {k} の面を含む。
方針：k と異なる頂点を選び、その頂点が singleton に属さないことを使う。
規約：零次元の空の horn には適用しない。
使われ方：面の nerve の収縮の終点。
-/
theorem hornFaceSingleton_mem (n : ℕ) [NeZero n] (k : Fin (n + 1)) :
    HornFaceSet n k (finiteChainSingleton (ULift.up.{u} k)) := by
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have h01 : (0 : Fin (n + 1)) ≠ Fin.last n := by
    intro h
    have h' := congrArg Fin.val h
    simp only [Fin.val_zero, Fin.val_last] at h'
    omega
  obtain ⟨j, hj⟩ : ∃ j : Fin (n + 1), j ≠ k := by
    by_cases h : k = 0
    · exact ⟨Fin.last n, fun h' => h01 ((h'.trans h).symm)⟩
    · exact ⟨0, Ne.symm h⟩
  refine ⟨j, hj, ?_⟩
  simpa only [finiteChainSingleton, finiteChainOfFinset, Finset.mem_singleton,
    ULift.up.injEq] using hj

/--
概要：正次元 horn の面の部分順序集合の nerve の包含は anodyne である。
方針：頂点 k の追加を経由する、部分対象を保つ二段階の収縮を使う。
規約：Moss 原論文 Proposition 2.19 の面の模型。細分との同型は別の証明項目。
使われ方：細分された horn の anodyne 性への比較。
-/
theorem hornFaceInclusion_anodyne (n : ℕ) [NeZero n] (k : Fin (n + 1)) :
    SSet.anodyneExtensions (nerveMap (hornFaceInclusion.{u} n k).monotone.functor) := by
  exact orderSubtypeNerve_anodyne (HornFaceSet n k) (finiteChainSingleton (ULift.up k))
    (hornFaceSingleton_mem n k) (hornFaceAddVertex n k) (hornFaceAddVertex_mem n k)
    (fun s => Finset.subset_insert _ _)
    (fun s => Finset.singleton_subset_iff.mpr (Finset.mem_insert_self _ _))

end SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor
