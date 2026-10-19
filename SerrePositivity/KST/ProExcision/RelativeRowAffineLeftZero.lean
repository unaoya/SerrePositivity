module
public import SerrePositivity.KST.ProExcision.RelativeRowAffineSequence

/-!
# 実行側 rank 余極限における左乗法の零化

概要：通常の行側安定化の実余極限上で指定元の左乗法を零化する。
方針：各成分が実行左乗法である自然変換を作り、有限 rank の零化を各脚へ適用する。
規約：KST Proposition 4.14、SW92 §1.2。安定モノイドの H_* との模型比較は別界面。
使われ方：整数作用への移送の行側入力。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.ProExcision
open CategoryTheory Limits Opposite
open scoped Simplicial

/-- 概要：実行側相対順序列の左乗法の実自然変換。
方針：実相対自然同型で列側の実右乗法を移す。各成分の実左乗法との同定を下で証明する。
規約：SW92 §1.2。零性を定義に含めない。使われ方：実余極限の誘導写像。 -/
def NonUnitalSimplicialRing.relativeRowAffineLeftNatTrans
    (I : NonUnitalSimplicialRing.{u}) (a : I.obj (op ⦋0⦌))
    (F : SSet.{u} ⥤ ModuleCat.{u} ℤ) {i : ℕ} (M : SimplicialHomologyModel F i) :
    I.relativeRowAffineRankSequence F ⟶ I.relativeRowAffineRankSequence F :=
  (I.relativeRowAffineComparisonNatIso F M).inv ≫
    I.reverseOpposite.relativeAffineRightNatTrans (MulOpposite.op a) F ≫
      (I.relativeRowAffineComparisonNatIso F M).hom

/-- 概要：実行側自然変換の各成分は通常の実左乗法写像。
方針：実相対同型の乗法正方形と実逆射を合成する。
規約：KST Proposition 4.14、SW92 §1.2。使われ方：実有限 rank 零化との接続。 -/
lemma NonUnitalSimplicialRing.relativeRowAffineLeftNatTrans_app
    (I : NonUnitalSimplicialRing.{u}) (a : I.obj (op ⦋0⦌))
    (F : SSet.{u} ⥤ ModuleCat.{u} ℤ) {i : ℕ} (M : SimplicialHomologyModel F i) (n : ℕ) :
    (I.relativeRowAffineLeftNatTrans a F M).app n = I.relativeRowAffineLeftMap a n F := by
  change (I.reverseOppositeRelativeAffineIso n F M).inv ≫
      (relativeBarPairMap F
        (I.reverseOpposite.columnRightActionHom (MulOpposite.op a) n).toPairMap ≫
          (I.reverseOppositeRelativeAffineIso n F M).hom) = _
  rw [relativeBarPairMap_toPairMap, I.reverseOppositeRelativeAffineIso_multiplication,
    Iso.inv_hom_id_assoc]

/-- 概要：実行側相対余極限への左乗法の実誘導写像。
方針：各成分が実左乗法である実自然変換を余極限関手に写す。
規約：SW92 §1.2。零性を定義しない。使われ方：有限 rank の実零化の安定化。 -/
def NonUnitalSimplicialRing.relativeRowAffineLeftColimitMap
    (I : NonUnitalSimplicialRing.{u}) (a : I.obj (op ⦋0⦌))
    (F : SSet.{u} ⥤ ModuleCat.{u} ℤ) {i : ℕ} (M : SimplicialHomologyModel F i) :
    I.relativeRowAffineColimit F ⟶ I.relativeRowAffineColimit F :=
  colimMap (I.relativeRowAffineLeftNatTrans a F M)

/-- 概要：実行側余極限への各脚の前の左乗法は零。
方針：rank を i だけ増やして行側の有限 rank 零化と実余極限の可換性を使う。
規約：KST Proposition 4.14、SW92 §1.2。使われ方：実余極限の外延性による零化。 -/
lemma NonUnitalSimplicialRing.relativeRowAffineLeft_leg_zero
    (I : NonUnitalSimplicialRing.{u}) (a : I.obj (op ⦋0⦌))
    (F : SSet.{u} ⥤ ModuleCat.{u} ℤ) (hF : SSet.anodyneExtensions.IsInvertedBy F)
    {i : ℕ} (M : SimplicialHomologyModel F i) (n : ℕ) :
    I.relativeRowAffineLeftMap a n F ≫ I.relativeRowAffineInclusion F n = 0 := by
  have hz : I.relativeRowAffineLeftMap a n F ≫
      (I.relativeRowAffineRankSequence F).map (homOfLE (Nat.le_add_right n i)) = 0 := by
    rw [I.relativeRowAffineRankSequence_map F M]
    exact I.rowAffineLeft_then_block_zero a n i F hF M (le_refl i)
  calc
    I.relativeRowAffineLeftMap a n F ≫ I.relativeRowAffineInclusion F n =
        I.relativeRowAffineLeftMap a n F ≫
          (I.relativeRowAffineRankSequence F).map (homOfLE (Nat.le_add_right n i)) ≫
            I.relativeRowAffineInclusion F (n + i) := by
      exact congrArg (fun t ↦ I.relativeRowAffineLeftMap a n F ≫ t)
        (colimit.w (I.relativeRowAffineRankSequence F) (homOfLE (Nat.le_add_right n i))).symm
    _ = 0 := by rw [← Category.assoc, hz, Limits.zero_comp]

/-- 概要：通常の実行側 rank 余極限上の左乗法は零。
方針：実誘導射を各有限 rank の脚で評価し、実行側の有限 rank 零化を適用する。
規約：KST Proposition 4.14、SW92 §1.2。中心性・乗法単射性を使わない強い相対零化。
使われ方：実安定ホモロジーとの模型比較を介した整数作用への移送。 -/
theorem NonUnitalSimplicialRing.relativeRowAffineLeftColimitMap_zero
    (I : NonUnitalSimplicialRing.{u}) (a : I.obj (op ⦋0⦌))
    (F : SSet.{u} ⥤ ModuleCat.{u} ℤ) (hF : SSet.anodyneExtensions.IsInvertedBy F)
    {i : ℕ} (M : SimplicialHomologyModel F i) :
    I.relativeRowAffineLeftColimitMap a F M = 0 := by
  apply (colimit.isColimit (I.relativeRowAffineRankSequence F)).hom_ext
  intro n
  rw [Limits.comp_zero]
  change colimit.ι (I.relativeRowAffineRankSequence F) n ≫
    colimMap (I.relativeRowAffineLeftNatTrans a F M) = 0
  rw [ι_colimMap, I.relativeRowAffineLeftNatTrans_app]
  exact I.relativeRowAffineLeft_leg_zero a F hF M n

end SerrePositivity.KST.ProExcision
