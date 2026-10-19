module
public import SerrePositivity.KST.ProExcision.OppositeBlockCoherence
public import SerrePositivity.KST.ProExcision.ColumnRowAffineIso

/-!
# 列側・行側の実比較と通常のブロック安定化の正方形

概要：反対転置の実半直積同型が通常の有限 rank 安定化と可換であることを証明する。
方針：行列ブロックとベクトルの零埋めの実比較を各成分に適用する。
規約：KST Proposition 4.14、SW92 §1.2。使われ方：実行側の安定零化への移送。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.ProExcision
open CategoryTheory Opposite Comparison

/-- 概要：実半直積の反対転置は通常のブロック安定化と可換。
方針：基底の実反対転置とファイバーの実零埋めの可換性を使う。
規約：SW92 §1.2。使われ方：実 bar の rank 遷移の比較。 -/
lemma NonUnitalSimplicialRing.reverseOppositeAffineIso_block
    (I : NonUnitalSimplicialRing.{u}) (n m : ℕ) :
    (I.reverseOpposite.columnBlockOverHom n m).total ≫
        (I.reverseOppositeAffineIso (n + m)).hom =
      (I.reverseOppositeAffineIso n).hom ≫ monoidReverseOppositeMap (I.rowAffineBlockMap n m) := by
  apply NatTrans.ext
  funext k
  apply MonCat.hom_ext
  apply MonoidHom.ext
  intro x
  apply MulOpposite.unop_injective
  apply MulOpposite.unop_injective
  apply ActionProduct.ext
  · apply MulOpposite.unop_injective
    apply Subtype.ext
    exact congrArg MulOpposite.unop
      (integerUnitizationMatrixOpEquiv_block (I.obj k) n m x.base.val)
  · exact integerUnitizationIdealOpVector_block (I.obj k) n m x.fiber

/-- 概要：実 bar 同型は通常の有限 rank 安定化と可換。
方針：実単体的正方形と対角全反転の自然性を合成する。
規約：KST Proposition 4.14、SW92 §1.2。使われ方：実 H_* 比較の rank 自然性。 -/
lemma NonUnitalSimplicialRing.reverseOppositeAffineBarIso_block
    (I : NonUnitalSimplicialRing.{u}) (n m : ℕ) :
    monoidBarMap (I.reverseOpposite.columnBlockOverHom n m).total ≫
        (I.reverseOppositeAffineBarIso (n + m)).hom =
      (I.reverseOppositeAffineBarIso n).hom ≫
        SSet.opFunctor.map (monoidBarMap (I.rowAffineBlockMap n m)) := by
  change monoidBarMap _ ≫ (monoidBarMap (I.reverseOppositeAffineIso (n + m)).hom ≫
      (monoidBarReverseOppositeIso (I.rowAffine (n + m))).hom) =
    (monoidBarMap (I.reverseOppositeAffineIso n).hom ≫
      (monoidBarReverseOppositeIso (I.rowAffine n)).hom) ≫ _
  rw [← Category.assoc, ← monoidBarMap_comp, I.reverseOppositeAffineIso_block,
    monoidBarMap_comp, Category.assoc, monoidBarReverseOppositeIso_natural, ← Category.assoc]

/-- 概要：実 H_* 同型は通常の有限 rank 安定化と可換。
方針：実 bar 正方形と実鎖反転の自然性を合成する。
規約：SW92 §1.2。使われ方：実相対加群の通常の rank 遷移への降下。 -/
lemma NonUnitalSimplicialRing.reverseOppositeAffineHomologyIso_block
    (I : NonUnitalSimplicialRing.{u}) (n m : ℕ)
    (F : SSet.{u} ⥤ ModuleCat.{u} ℤ) {i : ℕ} (hF : SimplicialHomologyModel F i) :
    F.map (monoidBarMap (I.reverseOpposite.columnBlockOverHom n m).total) ≫
        (I.reverseOppositeAffineHomologyIso (n + m) F hF).hom =
      (I.reverseOppositeAffineHomologyIso n F hF).hom ≫
        F.map (monoidBarMap (I.rowAffineBlockMap n m)) := by
  change F.map _ ≫ (F.map (I.reverseOppositeAffineBarIso (n + m)).hom ≫
      hF.reversalNatIso.hom.app (monoidBar (I.rowAffine (n + m)))) =
    (F.map (I.reverseOppositeAffineBarIso n).hom ≫
      hF.reversalNatIso.hom.app (monoidBar (I.rowAffine n))) ≫ _
  rw [← Category.assoc, ← F.map_comp, I.reverseOppositeAffineBarIso_block,
    F.map_comp, Category.assoc]
  have hn := hF.reversalNatIso.hom.naturality (monoidBarMap (I.rowAffineBlockMap n m))
  change F.map (SSet.opFunctor.map (monoidBarMap (I.rowAffineBlockMap n m))) ≫ _ = _ at hn
  rw [hn, ← Category.assoc]

end SerrePositivity.KST.ProExcision
