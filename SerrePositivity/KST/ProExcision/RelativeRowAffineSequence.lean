module
public import SerrePositivity.KST.ProExcision.RowRelativeBlockMap
public import SerrePositivity.KST.ProExcision.RelativeAffineRightMultiplication

/-!
# 実行側相対加群の通常の rank 余極限

概要：通常の行側ブロック安定化の実順序列を構成し、列側の実順序列と自然に比較する。
方針：各次数の実相対同型を通常のブロック正方形で束ねる。
規約：KST Proposition 4.14、SW92 §1.2。安定モノイドの H_* との同定とは区別する。
使われ方：実行側相対余極限上の左乗法の零化。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.ProExcision
open CategoryTheory Limits

/-- 概要：通常の行側ブロック安定化による実相対加群の順序列。
方針：実一座標遷移を順序列の関手にする。
規約：SW92 §1.2。使われ方：実行側の相対余極限。 -/
def NonUnitalSimplicialRing.relativeRowAffineRankSequence (I : NonUnitalSimplicialRing.{u})
    (F : SSet.{u} ⥤ ModuleCat.{u} ℤ) : ℕ ⥤ ModuleCat.{u} ℤ :=
  Functor.ofSequence (fun n ↦ I.relativeRowAffineBlockMap n 1 F)

/-- 概要：通常の行側相対加群の実 rank 余極限。
方針：実順序列の ModuleCat における余極限を取る。
規約：KST Proposition 4.14。安定 H_* との模型同定は別の工程。
使われ方：行側の有限 rank 零化の安定化。 -/
def NonUnitalSimplicialRing.relativeRowAffineColimit (I : NonUnitalSimplicialRing.{u})
    (F : SSet.{u} ⥤ ModuleCat.{u} ℤ) : ModuleCat.{u} ℤ :=
  colimit (I.relativeRowAffineRankSequence F)

/-- 概要：有限 rank の行側相対加群から実余極限への脚。
方針：実順序余極限の標準脚を用いる。
規約：SW92 §1.2。使われ方：有限段階の実零化の移送。 -/
def NonUnitalSimplicialRing.relativeRowAffineInclusion (I : NonUnitalSimplicialRing.{u})
    (F : SSet.{u} ⥤ ModuleCat.{u} ℤ) (n : ℕ) :
    I.relativeRowAffineModule n F ⟶ I.relativeRowAffineColimit F :=
  colimit.ι (I.relativeRowAffineRankSequence F) n

/-- 概要：反対係数の列側と元の行側の実相対 rank 順序列の自然同型。
方針：各有限 rank の実相対同型を通常の一座標遷移の実正方形で束ねる。
規約：KST Proposition 4.14、SW92 §1.2。使われ方：任意の有限 rank 遷移の同定。 -/
def NonUnitalSimplicialRing.relativeRowAffineComparisonNatIso
    (I : NonUnitalSimplicialRing.{u}) (F : SSet.{u} ⥤ ModuleCat.{u} ℤ)
    {i : ℕ} (M : SimplicialHomologyModel F i) :
    I.reverseOpposite.relativeAffineRankSequence F ≅ I.relativeRowAffineRankSequence F := by
  let t : I.reverseOpposite.relativeAffineRankSequence F ⟶ I.relativeRowAffineRankSequence F :=
    NatTrans.ofSequence (fun n ↦ (I.reverseOppositeRelativeAffineIso n F M).hom) (by
      intro n
      rw [show (I.reverseOpposite.relativeAffineRankSequence F).map
          (homOfLE (Nat.le_add_right n 1)) =
            relativeBarPairMap F (I.reverseOpposite.columnBlockOverHom n 1).toPairMap from
              Functor.ofSequence_map_homOfLE_succ _ _,
        show (I.relativeRowAffineRankSequence F).map (homOfLE (Nat.le_add_right n 1)) =
          I.relativeRowAffineBlockMap n 1 F from Functor.ofSequence_map_homOfLE_succ _ _]
      exact I.reverseOppositeRelativeAffineIso_block n 1 F M)
  exact NatIso.ofComponents (fun n ↦ I.reverseOppositeRelativeAffineIso n F M)
    (fun f ↦ t.naturality f)

/-- 概要：行側順序列の任意の有限遷移は通常の一度のブロック安定化。
方針：実列側順序列の遷移と実相対自然同型の自然性を使う。
規約：SW92 §1.2。使われ方：必要な rank まで増やす実零化。 -/
lemma NonUnitalSimplicialRing.relativeRowAffineRankSequence_map
    (I : NonUnitalSimplicialRing.{u}) (F : SSet.{u} ⥤ ModuleCat.{u} ℤ)
    {i : ℕ} (M : SimplicialHomologyModel F i) (n m : ℕ) :
    (I.relativeRowAffineRankSequence F).map (homOfLE (Nat.le_add_right n m)) =
      I.relativeRowAffineBlockMap n m F := by
  have hn := (I.relativeRowAffineComparisonNatIso F M).hom.naturality
    (homOfLE (Nat.le_add_right n m))
  change (I.reverseOpposite.relativeAffineRankSequence F).map _ ≫
      (I.reverseOppositeRelativeAffineIso (n + m) F M).hom =
    (I.reverseOppositeRelativeAffineIso n F M).hom ≫
      (I.relativeRowAffineRankSequence F).map _ at hn
  rw [I.reverseOpposite.relativeAffineRankSequence_map] at hn
  apply (cancel_epi (I.reverseOppositeRelativeAffineIso n F M).hom).1
  exact hn.symm.trans (I.reverseOppositeRelativeAffineIso_block n m F M)

end SerrePositivity.KST.ProExcision
