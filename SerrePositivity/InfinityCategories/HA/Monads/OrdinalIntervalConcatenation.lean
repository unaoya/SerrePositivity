module

public import SerrePositivity.InfinityCategories.HA.Monads.OrdinalGlueGalois

/-!
概要：区間表示が順序和を端点共有の射へ送ることを全射で示す。
方針：最大元付加の二つの計算と、構成済みのGalois随伴の一意性を使う。
規約：空の有限順序集合を除外しない。
使われ方：HA Proposition 4.7.3.3、Riehl–Verity Remark 3.3.8 の混合水平合成の比較。
Kerodon Remark 6.2.1.4（Tag 02EN）。
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory

namespace SerrePositivity.InfinityCategories.HA.Monads

variable {m n p q : ℕ}

/-- 概要：順序和の最後への最大元付加は右因子への最大元付加。
方針：最後の点と元の二つの区間で計算する。規約：両因子とも空も許す。
使われ方：Riehl–Verity Remark 3.3.8 の区間表示の積の照合。 -/
lemma ordinalAppend_adjoinTop (f : Fin m →o Fin n) (g : Fin p →o Fin q) :
    ordinalAdjoinTop (ordinalAppend f g) =
      ordinalAppend (m := m) (n := n) (p := p + 1) (q := q + 1) f (ordinalAdjoinTop g) := by
  apply OrderHom.ext
  funext i
  apply Fin.ext
  cases i using Fin.lastCases with
  | last =>
    have hl := congrArg Fin.val (ordinalAdjoinTop_last (ordinalAppend f g))
    have hv := ordinalAppend_val_right f (ordinalAdjoinTop g) (Fin.last (m + p))
      (by change m ≤ m + p; omega)
    simp only [Fin.val_last, Nat.add_sub_cancel_left] at hv
    change (ordinalAppend f (ordinalAdjoinTop g) (Fin.last (m + p))).val =
      n + (ordinalAdjoinTop g (Fin.last p)).val at hv
    have hv' : (ordinalAppend f (ordinalAdjoinTop g) (Fin.last (m + p))).val = n + q := by
      simpa only [ordinalAdjoinTop_last, Fin.val_last] using hv
    exact hl.trans hv'.symm
  | cast i =>
    rw [ordinalAdjoinTop_castSucc]
    change (ordinalAppend f g i).val = (ordinalAppend f (ordinalAdjoinTop g) i.castSucc).val
    by_cases hi : i.val < m
    · calc
        _ = (f ⟨i.val, hi⟩).val := ordinalAppend_val_left f g i hi
        _ = _ := (ordinalAppend_val_left f (ordinalAdjoinTop g) i.castSucc hi).symm
    · calc
        _ = n + (g ⟨i.val - m, by have := i.isLt; omega⟩).val :=
          ordinalAppend_val_right f g i (by omega)
        _ = n + (ordinalAdjoinTop g
              (⟨i.val - m, by have := i.isLt; omega⟩ : Fin p).castSucc).val := by
          rw [ordinalAdjoinTop_castSucc]
          rfl
        _ = _ := (ordinalAppend_val_right f (ordinalAdjoinTop g) i.castSucc
          (by change m ≤ i.val; omega)).symm

/-- 概要：端点共有の最後への最大元付加も右因子に移る。
方針：共有点の前後と新しい最後の点で同じ値を計算する。
規約：元の二つの区間は非空。使われ方：Riehl–Verity Remark 3.3.8 の混合合成の回収。 -/
lemma ordinalGlue_adjoinTop (f : Fin (m + 1) →o Fin (n + 1))
    (g : Fin (p + 1) →o Fin (q + 1)) :
    ordinalGlue (p := p + 1) (q := q + 1) f (ordinalAdjoinTop g) =
      ordinalAdjoinTop (ordinalGlue f g) := by
  apply OrderHom.ext
  funext i
  apply Fin.ext
  cases i using Fin.lastCases with
  | last =>
    have hl := congrArg Fin.val (ordinalAdjoinTop_last (ordinalGlue f g))
    have hv := ordinalGlue_val_of_lt f (ordinalAdjoinTop g) (Fin.last (m + p + 1))
      (by change m < m + p + 1; omega)
    simp only [Fin.val_last] at hv
    have hp : m + p + 1 - m = p + 1 := by omega
    simp only [hp] at hv
    change (ordinalGlue f (ordinalAdjoinTop g) (Fin.last (m + p + 1))).val =
      n + (ordinalAdjoinTop g (Fin.last (p + 1))).val at hv
    have hv' : (ordinalGlue f (ordinalAdjoinTop g) (Fin.last (m + p + 1))).val =
        n + q + 1 := by
      simpa only [ordinalAdjoinTop_last, Fin.val_last, Nat.add_assoc] using hv
    convert hv'.trans hl.symm using 1
  | cast i =>
    have hv : (ordinalGlue f (ordinalAdjoinTop g) i.castSucc).val =
        (ordinalGlue f g i).val := by
      by_cases hi : i.val ≤ m
      · calc
          _ = (f ⟨i.val, by omega⟩).val :=
            ordinalGlue_val_of_le f (ordinalAdjoinTop g) i.castSucc hi
          _ = _ := (ordinalGlue_val_of_le f g i hi).symm
      · calc
          _ = n + (ordinalAdjoinTop g
              (⟨i.val - m, by have := i.isLt; omega⟩ : Fin (p + 1)).castSucc).val :=
            ordinalGlue_val_of_lt f (ordinalAdjoinTop g) i.castSucc (by change m < i.val; omega)
          _ = n + (g ⟨i.val - m, by have := i.isLt; omega⟩).val := by
            rw [ordinalAdjoinTop_castSucc]
            rfl
          _ = _ := (ordinalGlue_val_of_lt f g i (by omega)).symm
    exact hv.trans (congrArg Fin.val (ordinalAdjoinTop_castSucc (ordinalGlue f g) i)).symm

/-- 概要：順序和の区間表示は区間表示同士の端点共有の射。
方針：構成済みのGalois条件と、同じ右随伴を持つ左随伴の一意性を使う。
規約：全て実際の有限単調射の等式。使われ方：Riehl–Verity Remark 3.3.8 のirの積。 -/
lemma ordinalIntervalMap_append (f : Fin m →o Fin n) (g : Fin p →o Fin q) :
    ordinalIntervalMap (ordinalAppend f g) =
      ordinalGlue (ordinalIntervalMap f) (ordinalIntervalMap g) := by
  have hg : ordinalRightAdjoint (ordinalIntervalMap g) (ordinalIntervalMap_zero g) =
      ordinalAdjoinTop g := ordinal_right_left (ordinalAdjoinTop g) (ordinalAdjoinTop_last g)
  have h := ordinalGlue_interval_gc f (ordinalIntervalMap g) (ordinalIntervalMap_zero g)
  rw [hg, ← ordinalAppend_adjoinTop] at h
  apply OrderHom.ext
  funext i
  exact (ordinalIntervalMap_gc (ordinalAppend f g)).l_unique h (fun _ => rfl)

/-- 概要：既存の非空の順序和の射と同じ値の表示を照合する。
方針：同じFin.addCasesと添字の輸送を展開する。規約：元の単体圏の射を変えない。
使われ方：HA Proposition 4.7.3.3 の既存の水平合成と値の表示の検収。 -/
lemma simplexTensorHomOf_append {X Y Z W : SimplexCategory} (f : X ⟶ Y) (g : Z ⟶ W) :
    (AugmentedSimplexCategory.tensorHomOf f g).toOrderHom =
      ordinalAppendNonempty f.toOrderHom g.toOrderHom := by
  apply OrderHom.ext
  funext i
  apply Fin.ext
  simp [AugmentedSimplexCategory.tensorHomOf, SimplexCategory.comp_toOrderHom,
    SimplexCategory.mkHom, ordinalAppendNonempty, ordinalAppend, OrderHom.comp,
    OrderIso.toOrderEmbedding, OrderEmbedding.toOrderHom, Fin.castOrderIso]
  rfl

end SerrePositivity.InfinityCategories.HA.Monads
