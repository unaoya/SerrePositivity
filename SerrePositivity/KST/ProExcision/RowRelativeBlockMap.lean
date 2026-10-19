module
public import SerrePositivity.KST.ProExcision.ColumnRowBlockSquare
public import SerrePositivity.KST.ProExcision.RowRelativeLeftMultiplication
public import SerrePositivity.KST.ProExcision.ColumnRightBlockCoherence

/-!
# 行側相対項の通常の安定化と有限 rank の零化

概要：通常の実ブロック安定化を相対商へ降ろし、列側の Claim 4.15 を行側へ移す。
方針：実相対同型の乗法・rank 自然性を合成し、実列側零化を適用する。
規約：KST Proposition 4.14、SW92 §1.2 の行側。係数の可換性は使わない。
使われ方：行側の実安定左乗法の零化。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.ProExcision
open CategoryTheory Opposite Comparison
open scoped Simplicial

/-- 概要：行側相対加群の通常の有限 rank 安定化の実写像。
方針：実 ĜL ブロック和と実行側半直積の零埋めの正方形を商へ降ろす。
規約：SW92 §1.2。使われ方：実行側相対加群の順序列。 -/
def NonUnitalSimplicialRing.relativeRowAffineBlockMap
    (I : NonUnitalSimplicialRing.{u}) (n m : ℕ) (F : SSet.{u} ⥤ ModuleCat.{u} ℤ) :
    I.relativeRowAffineModule n F ⟶ I.relativeRowAffineModule (n + m) F :=
  relativeModuleMap _ _ (F.map (monoidBarMap (I.hatGLBlockMap n m)))
    (F.map (monoidBarMap (I.rowAffineBlockMap n m))) (by
      rw [← F.map_comp, ← F.map_comp, ← monoidBarMap_comp, ← monoidBarMap_comp,
        I.rowAffineBlockMap_section])

/-- 概要：実相対同型は通常の行側・列側ブロック安定化と可換。
方針：実相対商の合成則と全空間の実 H_* 正方形を使う。
規約：KST Proposition 4.14、SW92 §1.2。使われ方：有限 rank の実零化の移送。 -/
lemma NonUnitalSimplicialRing.reverseOppositeRelativeAffineIso_block
    (I : NonUnitalSimplicialRing.{u}) (n m : ℕ)
    (F : SSet.{u} ⥤ ModuleCat.{u} ℤ) {i : ℕ} (M : SimplicialHomologyModel F i) :
    relativeBarPairMap F (I.reverseOpposite.columnBlockOverHom n m).toPairMap ≫
        (I.reverseOppositeRelativeAffineIso (n + m) F M).hom =
      (I.reverseOppositeRelativeAffineIso n F M).hom ≫ I.relativeRowAffineBlockMap n m F := by
  unfold relativeBarPairMap relativeRowAffineBlockMap reverseOppositeRelativeAffineIso relativeModuleIso
  rw [relativeModuleMap_comp, relativeModuleMap_comp]
  apply relativeModuleMap_eq_of_right_eq
  exact I.reverseOppositeAffineHomologyIso_block n m F M

/-- 概要：行の左乗法の後の通常の安定化の実相対写像は低次で零。
方針：実相対同型の乗法・rank 自然性により列側 Claim 4.15 の実零化へ帰着する。
規約：KST Proposition 4.14、SW92 §1.2。中心性・乗法単射性はこの零化には不要。
使われ方：実行側の安定相対零化の有限 rank の入力。 -/
theorem NonUnitalSimplicialRing.rowAffineLeft_then_block_zero
    (I : NonUnitalSimplicialRing.{u}) (a : I.obj (op ⦋0⦌)) (n m : ℕ)
    (F : SSet.{u} ⥤ ModuleCat.{u} ℤ) (hF : SSet.anodyneExtensions.IsInvertedBy F)
    {i : ℕ} (M : SimplicialHomologyModel F i) (hi : i ≤ m) :
    I.relativeRowAffineLeftMap a n F ≫ I.relativeRowAffineBlockMap n m F = 0 := by
  apply (cancel_epi (I.reverseOppositeRelativeAffineIso n F M).hom).1
  rw [Limits.comp_zero]
  calc
    (I.reverseOppositeRelativeAffineIso n F M).hom ≫
        (I.relativeRowAffineLeftMap a n F ≫ I.relativeRowAffineBlockMap n m F) =
      (relativeBarMap F (I.reverseOpposite.columnRightActionHom (MulOpposite.op a) n) ≫
        relativeBarPairMap F (I.reverseOpposite.columnBlockOverHom n m).toPairMap) ≫
          (I.reverseOppositeRelativeAffineIso (n + m) F M).hom := by
      rw [← Category.assoc, ← I.reverseOppositeRelativeAffineIso_multiplication,
        Category.assoc, ← I.reverseOppositeRelativeAffineIso_block, ← Category.assoc]
    _ = 0 := by
      rw [← relativeBarPairMap_toPairMap, ← relativeBarPairMap_comp,
        I.reverseOpposite.columnRight_then_block,
        claim415 I.reverseOpposite (MulOpposite.op a) n m F hF M hi, Limits.zero_comp]

end SerrePositivity.KST.ProExcision
