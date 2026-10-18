module

public import SerrePositivity.EInfinity.Operad.AdjacentTailSplitLast
public import SerrePositivity.EInfinity.Operad.SplitPairCoherence

/-!
# 尾の交換後の最後の分離の再帰

概要：Berger–Moerdijk §1 の末尾を固定する隣接交換後の分離を尾の分離へ帰着する。
方針：具体的な入力族へ移し、結合子の移送の自然性で尾の終域を正規化する。
規約：先頭と最後の因子は固定する。
使われ方：隣接交換と最後の分離の可換性の帰納段階を与える。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity

open CategoryTheory MonoidalCategory
open SerrePositivity.DifferentialGraded SerrePositivity.Coxeter

variable {A : Type u} [CommRing A]

attribute [local implicit_reducible] tensorFamily tensorFamilyAdjacentCastTail
  Fin.cases Fin.induction Fin.induction.go
attribute [local irreducible] HomologicalComplex.monoidalCategoryStruct tensorFamilySplitLast

/-- 概要：尾の隣接交換後の分離の終域を先頭と交換後の前半の尾、最後の因子で表す（Berger–Moerdijk §1）。
方針：持ち上げた交換の分離の終域の式と、前半のずらした交換の式を合成する。
規約：全入力族の交換位置は i.succ.castSucc。
使われ方：帰納段階で共通の終域を指定する。 -/
lemma tensorFamilyAdjacentSucc_splitLast_output_obj (n : ℕ)
    (V : Fin (n + 3) → Complex A) (i : Fin n) :
    tensorFamily (n + 2) (fun j => V (adjacentTransposition i.succ.castSucc j.castSucc)) ⊗
        V (adjacentTransposition i.succ.castSucc (Fin.last (n + 2))) =
      (V 0 ⊗ tensorFamily (n + 1) (fun j => V (adjacentTransposition i j).castSucc.succ)) ⊗
        V (Fin.last (n + 2)) := by
  have h := (tensorFamily_adjacentCastSucc_output_obj (n + 1) V i.succ).trans
    (congrArg (fun X : Complex A => X ⊗ V (Fin.last (n + 2)))
      (tensorFamily_adjacentSucc_obj n (fun j => V j.castSucc) i))
  exact h

/-- 概要：交換後の分離の終域の二つの移送は先頭と尾を明示した対象への移送に一致する（Berger–Moerdijk §1）。
方針：右 whisker の等式の射をテンソル対象の等式の射へ直し合成する。
規約：前半の交換後の対象の同定を最後の因子の左側に適用する。
使われ方：同型で後合成して可換性を比較する帰納法で用いる。 -/
lemma tensorFamilyAdjacentSucc_splitLast_output_hom (n : ℕ)
    (V : Fin (n + 3) → Complex A) (i : Fin n) :
    eqToHom (tensorFamily_adjacentCastSucc_output_obj (n + 1) V i.succ) ≫
        (eqToHom (tensorFamily_adjacentSucc_obj n (fun j => V j.castSucc) i) ▷
          V (Fin.last (n + 2))) =
      eqToHom (tensorFamilyAdjacentSucc_splitLast_output_obj n V i) := by
  conv_lhs =>
    arg 2
    rw [eqToHom_whiskerRight (tensorFamily_adjacentSucc_obj n (fun j => V j.castSucc) i)
      (V (Fin.last (n + 2)))]
  exact eqToHom_trans (tensorFamily_adjacentCastSucc_output_obj (n + 1) V i.succ)
    (congrArg (fun X : Complex A => X ⊗ V (Fin.last (n + 2)))
      (tensorFamily_adjacentSucc_obj n (fun j => V j.castSucc) i))

/-- 概要：実際の尾の交換後の分離は具体的な持ち上げた入力族の分離に一致する（Berger–Moerdijk §1）。
方針：入力族の等式による分離同型の比較を共通の始域と終域に適用する。
規約：先頭を分けた始域と最後の因子を分けた終域を使う。
使われ方：交換後の分離を先頭に関する再帰式で計算する。 -/
lemma tensorFamilyAdjacentSucc_splitLast_compare (n : ℕ)
    (V : Fin (n + 3) → Complex A) (i : Fin n) :
    eqToHom (tensorFamily_adjacentSucc_obj (n + 1) V i.castSucc).symm ≫
        (tensorFamilySplitLast (n + 2)
          (fun j => V (adjacentTransposition i.succ.castSucc j))).hom ≫
        eqToHom (tensorFamilyAdjacentSucc_splitLast_output_obj n V i) =
      eqToHom (tensorFamilyAdjacentCastTail_source_obj n V i).symm ≫
        (tensorFamilySplitLast (n + 2) (tensorFamilyAdjacentCastTail n V i)).hom ≫
        eqToHom (tensorFamilyAdjacentCastTail_output_obj n V i) := by
  exact tensorFamilySplitLast_compare (n + 2) (tensorFamilyAdjacentCastTail_eq n V i)
    (tensorFamilyAdjacentCastTail_source_obj n V i)
    (tensorFamily_adjacentSucc_obj (n + 1) V i.castSucc)
    (tensorFamilyAdjacentCastTail_output_obj n V i)
    (tensorFamilyAdjacentSucc_splitLast_output_obj n V i)

/-- 概要：持ち上げた尾の交換後の最後の分離は尾の分離を正規化した射から計算できる（Berger–Moerdijk §1）。
方針：分離の再帰式に結合子の移送の自然性を適用する。
規約：先頭と最後の因子を保ち、尾の前半のみ交換する。
使われ方：尾の隣接交換の帰納仮定を適用する。 -/
lemma tensorFamilyAdjacentCastTail_splitLast_rec (n : ℕ)
    (V : Fin (n + 3) → Complex A) (i : Fin n) :
    eqToHom (tensorFamilyAdjacentCastTail_source_obj n V i).symm ≫
        (tensorFamilySplitLast (n + 2) (tensorFamilyAdjacentCastTail n V i)).hom ≫
        eqToHom (tensorFamilyAdjacentCastTail_output_obj n V i) =
      (V 0 ◁ ((tensorFamilySplitLast (n + 1)
        (fun j => V (adjacentTransposition i.castSucc j).succ)).hom ≫
          eqToHom (tensorFamily_adjacentCastSucc_output_obj n (fun j => V j.succ) i))) ≫
        (α_ (V 0) (tensorFamily (n + 1) (fun j => V (adjacentTransposition i j).castSucc.succ))
          (V (Fin.last (n + 2)))).inv := by
  conv_lhs =>
    arg 2
    arg 1
    rw [tensorFamilySplitLast_succ (n + 1) (tensorFamilyAdjacentCastTail n V i)]
  simp only [eqToHom_refl, Category.id_comp]
  have hp : tensorFamily (n + 1) (fun j => V (adjacentTransposition i.castSucc j.castSucc).succ) =
      tensorFamily (n + 1) (fun j => V (adjacentTransposition i j).castSucc.succ) := by
    simp only [adjacentCastSucc_prefix]
  have hl : V (adjacentTransposition i.castSucc (Fin.last (n + 1))).succ =
      V (Fin.last (n + 2)) := by
    rw [adjacentCastSucc_last]
    rfl
  have h := @associator_inv_eqToHom_pair (Complex A) (by infer_instance) (by infer_instance)
    (V 0) _ _ _ _ hp hl
  simp only [tensorFamilyAdjacentCastTail, tensorFamily, Fin.castSucc_succ,
    Fin.castSucc_zero, Fin.cases_zero, Fin.cases_succ] at h ⊢
  dsimp only [Fin.cases, Fin.induction, Fin.induction.go, Fin.last,
    Fin.castSucc, Fin.castAdd, Fin.castLE, Fin.succ] at h ⊢
  simp only [Category.assoc]
  conv_lhs =>
    arg 2
    erw [← h]
  simp only [whiskerLeft_comp, Category.assoc]

/-- 概要：実際の尾の隣接交換後の最後の分離を尾の分離へ帰着する（Berger–Moerdijk §1）。
方針：具体的な入力族への比較と正規化した分離の再帰式を合成する。
規約：交換後の分離の始域と終域の移送を明示する。
使われ方：末尾を固定する任意の隣接交換の可換性の帰納段階へ直接適用する。 -/
lemma tensorFamilyAdjacentSucc_splitLast_rec (n : ℕ)
    (V : Fin (n + 3) → Complex A) (i : Fin n) :
    eqToHom (tensorFamily_adjacentSucc_obj (n + 1) V i.castSucc).symm ≫
        (tensorFamilySplitLast (n + 2)
          (fun j => V (adjacentTransposition i.succ.castSucc j))).hom ≫
        eqToHom (tensorFamilyAdjacentSucc_splitLast_output_obj n V i) =
      (V 0 ◁ ((tensorFamilySplitLast (n + 1)
        (fun j => V (adjacentTransposition i.castSucc j).succ)).hom ≫
          eqToHom (tensorFamily_adjacentCastSucc_output_obj n (fun j => V j.succ) i))) ≫
        (α_ (V 0) (tensorFamily (n + 1) (fun j => V (adjacentTransposition i j).castSucc.succ))
          (V (Fin.last (n + 2)))).inv := by
  exact (tensorFamilyAdjacentSucc_splitLast_compare n V i).trans
    (tensorFamilyAdjacentCastTail_splitLast_rec n V i)

end SerrePositivity.EInfinity
