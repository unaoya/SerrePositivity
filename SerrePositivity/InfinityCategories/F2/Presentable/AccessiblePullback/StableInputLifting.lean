module

public import SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback.AccessibleInputComparison
public import SerrePositivity.InfinityCategories.F2.Presentable.SlicePostcompEquivalenceLifting

/-!
概要：入力と標的を固定する後合成の同値持ち上げと全単体値。
方針：既存の coslice・slice 後合成の同値持ち上げを合成する。
規約：元の入力と標的を全単体上で固定する。
使われ方：比較同型から元の厳密な引き戻しの全余錐を回収する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback

/-- 概要：入力固定の二重後合成は各単体を元の固定始域後合成で送る。
方針：任意の Yoneda 族に全展開の等式を適用する。
規約：全次数で元の全余錐の値を保持する。
使われ方：厳密な引き戻しへの全図式の貼り合わせ。 -/
lemma stableInputPostcomp_val {K C B : SSet.{u}} (q : K ⟶ C) (f : C ⟶ B)
    (r : K ⟶ B) (hq : q ≫ f = r) (z : JoinCocone q) (t : JoinCocone r)
    (hz : z.val ≫ f = t.val) {n : ℕ}
    (σ : (sliceOver ((SSet.yonedaEquiv (X := sliceUnder q)).symm z)) _⦋n⦌) :
    ((stableInputPostcomp q f r hq z t hz).app (Opposite.op ⦋n⦌) σ).val =
      σ.val ≫ stableCoslicePostcomp q f r hq := by
  have h := stableInputPostcomp_uncurry q f r hq z t hz (SSet.yonedaEquiv.symm σ)
  rw [SSet.yonedaEquiv_symm_comp, sliceOverUncurry_yoneda,
    sliceOverUncurry_yoneda] at h
  exact h

/-- 概要：元の関手の同値持ち上げは入力と標的を固定する二重後合成へ移る。
方針：固定始域の後合成、標的上の後合成、表示同型の持ち上げを順に合成する。
規約：固定入力の有限性や新しい instance 仮定を要求しない。
使われ方：元の入力上の比較同型を厳密に一致する成分対へ持ち上げる。 -/
lemma stableInputPostcomp_equivalenceLifting {K C B : SSet.{u}}
    (q : K ⟶ C) (f : C ⟶ B) (hf : F1B.EquivalenceLifting f)
    (r : K ⟶ B) (hq : q ≫ f = r) (z : JoinCocone q) (t : JoinCocone r)
    (hz : z.val ≫ f = t.val) :
    F1B.EquivalenceLifting (stableInputPostcomp q f r hq z t hz) := by
  have hU : F1B.EquivalenceLifting (sliceUnderPostcomp q f) :=
    sliceUnderPostcomp_equivalenceLifting q f hf
  have hR : F1B.EquivalenceLifting (stableCoslicePostcomp q f r hq) := by
    intro A T i hi he
    have := hU i hi he
    dsimp only [stableCoslicePostcomp]
    infer_instance
  have hO : F1B.EquivalenceLifting (sliceOverPostcomp
      ((SSet.yonedaEquiv (X := sliceUnder q)).symm z) (stableCoslicePostcomp q f r hq)) :=
    sliceOverPostcomp_equivalenceLifting
      ((SSet.yonedaEquiv (X := sliceUnder q)).symm z) (stableCoslicePostcomp q f r hq) hR
  dsimp only [stableInputPostcomp]
  intro A T i hi he
  have := hO i hi he
  infer_instance

end SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback
