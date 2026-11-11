module

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.SubdivisionIntervals

/-!
# 複雑度作用素と拡張退化の交換

概要：Moss Lemma 26 (4) の作用素の交換則を証明する。
方針：和集合保存から singleton に帰着し、通常の退化の不等式を使う。
規約：Moss 2020 Lemma 26 (4)。射の合成の順序は Lean の前から後の順。
使われ方：Ex の regular pairing における複雑度の制御。

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
概要：特別な頂点以外では、退化の像と閾値との比較を元の頂点へ戻せる。
方針：δ^{k+1} の像で頂点を表し、σ^k との合成を打ち消す。
規約：Moss 2020 Lemma 26 (4) の生成元上の計算。
使われ方：複雑度の閾値を退化の前後で比較する。
-/
theorem liftedDegeneracy_le_iff_of_ne (n : ℕ) (h k : Fin (n + 1)) (hhk : h ≤ k)
    (i : ULift.{u} (Fin (n + 2))) (hi : i ≠ ULift.up k.succ) :
    liftedDegeneracy n k i ≤ ULift.up h ↔ i ≤ ULift.up h.castSucc := by
  change k.predAbove i.down ≤ h ↔ i.down ≤ h.castSucc
  have hne : i.down ≠ k.succ := fun h => hi (ULift.ext h)
  obtain ⟨j, hj⟩ := Fin.exists_succAbove_eq hne
  rw [← hj]
  have hpred : k.predAbove (k.succ.succAbove j) = j :=
    congrArg (fun f : SimplexCategory.mk n ⟶ SimplexCategory.mk n => f j)
      SimplexCategory.δ_comp_σ_succ
  rw [hpred, ← Fin.succAbove_succ_of_le k h hhk, Fin.succAbove_le_succAbove_iff]

/--
概要：拡張退化と小さい閾値の複雑度作用素は交換する。
方針：和を保つ写像の比較原理で singleton に帰着し、特別な頂点の場合を分ける。
規約：Moss 2020 Lemma 26 (4) の有限鎖上の式。
使われ方：pairing の像の複雑度を制御する。
-/
theorem finiteChainDegeneracy_cut (n : ℕ) (h k : Fin (n + 1)) (hhk : h ≤ k) :
    (finiteChainDegeneracy.{u} n k ∘ finiteChainCut (n + 1) (ULift.up h.castSucc)) =
      (finiteChainCut n (ULift.up h) ∘ finiteChainDegeneracy n k) := by
  apply finiteChainUnion_ext
    ((finiteChainDegeneracy_preservesUnion n k).comp
      (finiteChainCut_preservesUnion (n + 1) (ULift.up h.castSucc)))
    ((finiteChainCut_preservesUnion n (ULift.up h)).comp
      (finiteChainDegeneracy_preservesUnion n k))
  intro i
  change finiteChainDegeneracy n k
      (finiteChainCut (n + 1) (ULift.up h.castSucc) (finiteChainSingleton i)) =
    finiteChainCut n (ULift.up h) (finiteChainDegeneracy n k (finiteChainSingleton i))
  rw [finiteChainCut_singleton, finiteChainDegeneracy_singleton]
  by_cases hi : i = ULift.up k.succ
  · rw [ite_eq_left hi]
    subst i
    have hn : ¬ ULift.up k.succ ≤ (ULift.up h.castSucc : ULift.{u} (Fin (n + 2))) := by
      change ¬ k.succ ≤ h.castSucc
      change h.val ≤ k.val at hhk
      simp only [Fin.le_iff_val_le_val, Fin.val_succ, Fin.val_castSucc]
      omega
    rw [ite_eq_right hn, finiteChainDegeneracy_initialSegment, liftedDegeneracy_succ,
      finiteChainCut_initialSegment]
  · rw [ite_eq_right hi]
    have hle := liftedDegeneracy_le_iff_of_ne n h k hhk i hi
    by_cases hi' : i ≤ ULift.up h.castSucc
    · rw [ite_eq_left hi', finiteChainDegeneracy_singleton, ite_eq_right hi,
        finiteChainCut_singleton, ite_eq_left (hle.mpr hi')]
    · rw [ite_eq_right hi', finiteChainDegeneracy_initialSegment, finiteChainCut_singleton,
        ite_eq_right (fun hle' => hi' (hle.mp hle'))]

/--
概要：細分上の拡張退化と複雑度作用素の交換則。
方針：nerve の各頂点で有限鎖上の交換則を適用する。
規約：Moss 2020 Lemma 26 (4)、h≤k。
使われ方：Ex の regular pairing の複雑度の制御。
-/
@[reassoc] theorem subdivisionDegeneracyAt_cut (n : ℕ) (h k : Fin (n + 1)) (hhk : h ≤ k) :
    subdivisionCutAt.{u} (SimplexCategory.mk (n + 1)) h.castSucc ≫ subdivisionDegeneracyAt n k =
      subdivisionDegeneracyAt n k ≫ subdivisionCutAt (SimplexCategory.mk n) h := by
  apply NatTrans.ext
  funext d
  apply ConcreteCategory.hom_ext
  intro s
  apply nerve.ext_of_isThin
  funext i
  exact congrFun (finiteChainDegeneracy_cut n h k hhk) (s.obj i)

/--
概要：閾値 h<k で切ると、拡張退化と通常の退化の差は消える。
方針：singleton 上では特別な頂点だけを調べ、両者が同じ初期区間に送られることを使う。
規約：Moss 2020 Lemma 26 (6) の有限鎖上の式。
使われ方：pairing の対応先の退化性の制御。
-/
theorem finiteChainDegeneracy_cut_lt (n : ℕ) (h k : Fin (n + 1)) (hhk : h < k) :
    (finiteChainCut.{u} n (ULift.up h) ∘ finiteChainDegeneracy n k) =
      (finiteChainCut n (ULift.up h) ∘ fun s => s.map (liftedDegeneracy n k)) := by
  apply finiteChainUnion_ext
    ((finiteChainCut_preservesUnion n (ULift.up h)).comp
      (finiteChainDegeneracy_preservesUnion n k))
    ((finiteChainCut_preservesUnion n (ULift.up h)).comp
      (finiteChainMap_preservesUnion (liftedDegeneracy n k)))
  intro i
  change finiteChainCut n (ULift.up h) (finiteChainDegeneracy n k (finiteChainSingleton i)) =
    finiteChainCut n (ULift.up h) ((finiteChainSingleton i).map (liftedDegeneracy n k))
  rw [finiteChainDegeneracy_singleton, finiteChainMap_singleton]
  by_cases hi : i = ULift.up k.succ
  · rw [ite_eq_left hi]
    subst i
    rw [finiteChainCut_initialSegment, liftedDegeneracy_succ, finiteChainCut_singleton,
      ite_eq_right (show ¬ (ULift.up k : ULift.{u} (Fin (n + 1))) ≤ ULift.up h from
        not_le_of_gt hhk)]
  · rw [ite_eq_right hi]

/--
概要：小さい複雑度へ切った拡張退化は通常の細分退化に一致する。
方針：nerve の各頂点で有限鎖上の計算を使う。
規約：Moss 2020 Lemma 26 (6)、h<k。
使われ方：regular pairing の非退化性と複雑度の比較。
-/
@[reassoc] theorem subdivisionDegeneracyAt_cut_lt (n : ℕ) (h k : Fin (n + 1)) (hhk : h < k) :
    subdivisionDegeneracyAt.{u} n k ≫ subdivisionCutAt (SimplexCategory.mk n) h =
      SimplexCategory.sd.map (SimplexCategory.σ k) ≫ subdivisionCutAt (SimplexCategory.mk n) h := by
  apply NatTrans.ext
  funext d
  apply ConcreteCategory.hom_ext
  intro s
  apply nerve.ext_of_isThin
  funext i
  exact congrFun (finiteChainDegeneracy_cut_lt n h k hhk) (s.obj i)

end SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor
