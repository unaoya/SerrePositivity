module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ErasedEnumeration
public import Mathlib.Order.Hom.Set
public import Mathlib.Order.Preorder.Finite

/-!
# 降順番号付けと一点削除

概要：降順の番号付けは一意で、一座標を飛ばした番号付けも降順である。
方針：Fin の反転で増加する番号付けに直し、有限順序の自己同型の一意性を使う。
規約：削除後の相対順序を保つので追加の向きの符号は生じない。
使われ方：HA 1.3.1.16、Kerodon 2.5.9（Tag 00SC） の削除項と標準の降順評価の同定。

対応節は Kerodon 2.5（Tag 00ND）。
-/

@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories

/-- 概要：有限全順序集合の同じ長さの降順番号付けは一意である。
方針：番号を反転して厳密単調写像とし、全射性から像が同じであることを使う。
規約：部分型を含む任意の全順序集合に適用できる。
使われ方：Kerodon 2.5.9（Tag 00SC） の削除番号付けと標準番号付けの比較。 -/
lemma strictAnti_enumeration_unique {A : Type u} [LinearOrder A] {m : ℕ}
    (e f : Fin m ≃ A) (he : StrictAnti e) (hf : StrictAnti f) : e = f := by
  have h : (fun i : Fin m ↦ e i.rev) = (fun i : Fin m ↦ f i.rev) :=
    (he.comp Fin.rev_strictAnti).eq_of_range_eq
      (hf.comp Fin.rev_strictAnti) (by
        have he' : Function.Surjective (fun i : Fin m ↦ e i.rev) :=
          e.surjective.comp Fin.rev_bijective.2
        have hf' : Function.Surjective (fun i : Fin m ↦ f i.rev) :=
          f.surjective.comp Fin.rev_bijective.2
        exact (Set.range_eq_univ.mpr he').trans (Set.range_eq_univ.mpr hf').symm)
  ext i
  simpa using congrFun h i.rev

/-- 概要：既定の有限集合の番号付けは厳密に降順である。
方針：Fin の反転に昇順の順序同型を合成する。
規約：値は有限集合の部分型に取る。
使われ方：HA 1.3.1.16 の基本鎖の向きの確認。 -/
lemma descendingEnumeration_strictAnti {A : Type u} [LinearOrder A] (S : Finset A) :
    StrictAnti (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.descendingEnumeration S) :=
  (S.orderIsoOfFin rfl).strictMono.comp_strictAnti Fin.rev_strictAnti

/-- 概要：降順番号付けから一番号を飛ばした番号付けも降順である。
方針：succAbove は厳密単調で、削除番号付けの値は元の番号付けの値である。
規約：有限集合の部分型の順序を使う。
使われ方：Kerodon 2.5.9（Tag 00SC） の座標0面の向きが保存されること。 -/
lemma erasedEnumeration_strictAnti {A : Type u} [LinearOrder A] {S : Finset A} {m : ℕ}
    (e : Fin (m + 1) ≃ S) (he : StrictAnti e) (i : Fin (m + 1)) :
    StrictAnti (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.erasedEnumeration e i) := by
  intro j k hjk
  change (e (i.succAbove k)).val < (e (i.succAbove j)).val
  exact he (i.succAboveOrderEmb.strictMono hjk)

/-- 概要：削除した降順番号付けは残る集合の標準降順番号付けと等しい。
方針：両者が降順の全単射であることから一意性を使う。
規約：濃度の等式を引数に取り、添字の移送を挿入しない。
使われ方：HA 1.3.1.16 の削除面の評価を標準の向きへ同定する。 -/
lemma erasedEnumeration_eq_descending {A : Type u} [LinearOrder A] {S : Finset A} {m : ℕ}
    (e : Fin (m + 1) ≃ S) (he : StrictAnti e) (i : Fin (m + 1))
    (h : (S.erase (e i).val).card = m) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.erasedEnumeration e i =
      Fin.revPerm.trans ((S.erase (e i).val).orderIsoOfFin h).toEquiv := by
  apply strictAnti_enumeration_unique
  · exact erasedEnumeration_strictAnti e he i
  · exact ((S.erase (e i).val).orderIsoOfFin h).strictMono.comp_strictAnti Fin.rev_strictAnti

/-- 概要：降順番号付けの i 番目の点より大きい点の個数は i である。
方針：番号付けの逆によって大きい点の集合と Fin の Iio を全単射にする。
規約：比較は元の有限集合の順序による。
使われ方：HA 1.3.1.16 の座標境界の係数を dg nerve の削除係数へ合わせる。 -/
lemma strictAnti_enumeration_card_filter {A : Type u} [LinearOrder A]
    {S : Finset A} {m : ℕ} (e : Fin m ≃ S) (he : StrictAnti e) (i : Fin m) :
    (S.filter ((e i).val < ·)).card = i.val := by
  classical
  have h : (S.filter ((e i).val < ·)).card = (Finset.Iio i).card := by
    refine Finset.card_bij (fun a ha ↦ e.symm ⟨a, (Finset.mem_filter.mp ha).1⟩) ?_ ?_ ?_
    · intro a ha
      apply Finset.mem_Iio.mpr
      apply he.lt_iff_gt.mp
      change (e i).val < (e (e.symm ⟨a, (Finset.mem_filter.mp ha).1⟩)).val
      rw [e.apply_symm_apply]
      exact (Finset.mem_filter.mp ha).2
    · intro a ha b hb hab
      exact congrArg Subtype.val (e.symm.injective hab)
    · intro a ha
      refine ⟨(e a).val, Finset.mem_filter.mpr ⟨(e a).property, ?_⟩, e.symm_apply_apply a⟩
      exact he (Finset.mem_Iio.mp ha)
  exact h.trans (Fin.card_Iio i)

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
