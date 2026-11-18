module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.CoInsertion
public import SerrePositivity.DifferentialGraded.Complexes.TensorCoproduct
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.TensorAppend

/-!
模型。文献の定義との比較は後で
# 指定出力への余代入を前後ブロックで表示する

概要：Berger–Fresse §3.1 の実際の余代入射を前方・指定因子・後方のブロックで扱う。
方針：係数を前方ブロックの右へ動かし、指定因子への余演算後に前後を連結する。
規約：内側出力数と前後の長さは零も許す。
使われ方：実際の二段作用の純粋斉次元での評価。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.HomologicalComplex
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.TensorPowers

variable {A : Type u} [CommRing A]

attribute [local irreducible] HomologicalComplex.monoidalCategoryStruct
attribute [local implicit_reducible] _root_.SerrePositivity.TensorPowers.power

/-- 概要：前後ブロックを指定した余代入の内部射（BF §3.1）。
方針：係数を前方の右へ移し、指定因子へ作用させ、内側と後方、続いて前方を連結する。
規約：arity の等式による移送を前後から除いた実際の構成射の列。
使われ方：既存の tensorCoInsertionAction を同じブロック上で評価する。 -/
def coInsertionBlocks (K C : Complex A) (s n t : ℕ) (θ : C ⊗ K ⟶ power K n) :
    C ⊗ (power K s ⊗ (K ⊗ power K t)) ⟶ power K (s + (n + t)) :=
  parameterCross C (power K s) (K ⊗ power K t) ≫
    (power K s ◁ ((α_ C K (power K t)).inv ≫ (θ ▷ power K t) ≫
      (appendIso K n t).hom)) ≫ (appendIso K s (n + t)).hom

/-- 概要：実際の余代入射は前後ブロック表示の内部射と一致（BF §3.1）。
方針：反復テンソルの分割と arity の移送の往復を消す。
規約：前方長は指定位置、後方長は元の出力数から指定位置を引いた値。
使われ方：ブロックでの評価公式を元の余代入へ戻す。 -/
lemma tensorCoInsertionAction_on_blocks (K C : Complex A) (m n : ℕ) (i : Fin (m + 1))
    (θ : C ⊗ K ⟶ power K n) :
    (C ◁ ((appendIso K i.val (m - i.val + 1)).hom ≫
      eqToHom (congrArg (power K) (by omega : i.val + (m - i.val + 1) = m + 1)))) ≫
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorCoInsertionAction K C m n i θ =
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.coInsertionBlocks K C i.val n (m - i.val) θ ≫
      eqToHom (congrArg (power K) (by omega : i.val + (n + (m - i.val)) = m + n)) := by
  unfold _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorCoInsertionAction _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.coInsertionBlocks parameterCross
  dsimp only
  simp only [whiskerLeft_comp, Category.assoc]
  erw [← whiskerLeft_comp_assoc C, ← whiskerLeft_comp_assoc C,
    ← whiskerLeft_comp_assoc C]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp,
    Iso.hom_inv_id, whiskerLeft_id]
  rfl

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts
