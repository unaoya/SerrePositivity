module

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.SubdivisionIntervals

/-!
# 面写像と複雑度作用素の吸収則

概要：面写像の前で複雑度を切っても、後の複雑度作用素で差が消えることを示す。
方針：閾値を超える最大元の像を計算し、両辺を同じ初期区間へ送る。
規約：Moss 2020 Lemma 26 (5)。
使われ方：regular pairing の対応先の一意性に用いる。

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
概要：閾値を超える元を閾値の先へ送る単調写像では、前の切断は後の切断に吸収される。
方針：元の最大元が閾値以下かどうかで分け、像の最大元の保存を使う。
規約：Moss 2020 Lemma 26 (5) の有限集合上の計算の一般形。
使われ方：面写像の前後での複雑度の比較。
-/
theorem finiteChainCut_map_absorb {n m : ℕ}
    (f : ULift.{u} (Fin (n + 1)) →o ULift.{u} (Fin (m + 1)))
    (k : ULift.{u} (Fin (n + 1))) (l : ULift.{u} (Fin (m + 1)))
    (h : ∀ i, k < i → l < f i)
    (s : NonemptyFiniteChains (ULift.{u} (Fin (n + 1)))) :
    finiteChainCut m l ((finiteChainCut n k s).map f) = finiteChainCut m l (s.map f) := by
  change finiteChainCut m l
    ((if finiteChainMaximum s ≤ k then s else
      finiteChainInitialSegment n (finiteChainMaximum s)).map f) = _
  by_cases hs : finiteChainMaximum s ≤ k
  · rw [ite_eq_left hs]
  · rw [ite_eq_right hs]
    have hnot : ¬ f (finiteChainMaximum s) ≤ l := not_le_of_gt (h _ (lt_of_not_ge hs))
    change (if finiteChainMaximum ((finiteChainInitialSegment n (finiteChainMaximum s)).map f) ≤ l
      then _ else _) = (if finiteChainMaximum (s.map f) ≤ l then _ else _)
    simp only [finiteChainMaximum_map, finiteChainMaximum_initialSegment, hnot, ↓reduceIte]

/--
概要：面写像は閾値を超える頂点を、同じ番号の閾値の先へ送る。
方針：余面が頂点をそのまま保つ場合と一つずらす場合に分ける。
規約：Moss 2020 Lemma 26 (5) の閾値の条件。
使われ方：面写像への一般の吸収則の適用。
-/
theorem liftedFace_above (n : ℕ) (i : Fin (n + 2)) (k : Fin (n + 1))
    (x : ULift.{u} (Fin (n + 1))) (hx : (ULift.up k : ULift.{u} (Fin (n + 1))) < x) :
    (ULift.up k.castSucc : ULift.{u} (Fin (n + 2))) < liftedFace n i x := by
  change k.castSucc < i.succAbove x.down
  by_cases hi : x.down.castSucc < i
  · rw [Fin.succAbove_of_castSucc_lt _ _ hi]
    exact Fin.castSucc_lt_castSucc_iff.mpr hx
  · rw [Fin.succAbove_of_le_castSucc _ _ (le_of_not_gt hi)]
    exact Fin.castSucc_lt_succ_iff.mpr (le_of_lt hx)

/--
概要：細分された面写像の前の複雑度作用素は後の作用素に吸収される。
方針：有限鎖上の最大元の計算を nerve の各頂点で適用する。
規約：Moss 2020 Lemma 26 (5)、原典の n はこの宣言の n+1 に当たる。
使われ方：regular pairing の対応先の一意性と複雑度の制御。
-/
@[reassoc] theorem subdivisionCutAt_face_absorb (n : ℕ) (i : Fin (n + 2)) (k : Fin (n + 1)) :
    subdivisionCutAt.{u} (SimplexCategory.mk n) k ≫ SimplexCategory.sd.map (SimplexCategory.δ i) ≫
      subdivisionCutAt (SimplexCategory.mk (n + 1)) k.castSucc =
    SimplexCategory.sd.map (SimplexCategory.δ i) ≫
      subdivisionCutAt (SimplexCategory.mk (n + 1)) k.castSucc := by
  apply NatTrans.ext
  funext d
  apply ConcreteCategory.hom_ext
  intro s
  apply nerve.ext_of_isThin
  funext j
  exact finiteChainCut_map_absorb (liftedFace n i) (ULift.up k) (ULift.up k.castSucc)
    (fun x hx => liftedFace_above n i k x hx) (s.obj j)

end SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor
