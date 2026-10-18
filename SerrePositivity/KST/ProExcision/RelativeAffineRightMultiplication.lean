module
public import SerrePositivity.KST.ProExcision.RelativeAffineTransition
public import SerrePositivity.KST.ProExcision.ColumnRightBlockCoherence

/-!
# 相対アフィン加群の実余極限における右乗法の零化

概要：有限 rank の実右乗法を自然変換として安定化し、実余極限上で零と証明する。
方針：Claim 4.15 の通常の有限 rank 写像を順序列の遷移へ同定し、各脚で零化する。
規約：KST Proposition 4.14 の安定化の代数部分。安定 H_* との模型同定は別界面。
使われ方：実アフィン比較から像上の整数作用への移送。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.ProExcision
open CategoryTheory Limits Opposite
open scoped Simplicial

/-- 概要：有限 rank の相対加群の列の右乗法の実自然変換。
方針：同じ rank の実対射を取り、右乗法と通常の安定化の可換性を相対項へ写す。
規約：KST Proposition 4.14 の (id,a)。使われ方：実余極限への右乗法の誘導。 -/
def NonUnitalSimplicialRing.relativeAffineRightNatTrans (I : NonUnitalSimplicialRing.{u})
    (a : I.obj (op ⦋0⦌)) (F : SSet.{u} ⥤ ModuleCat.{u} ℤ) :
    I.relativeAffineRankSequence F ⟶ I.relativeAffineRankSequence F :=
  NatTrans.ofSequence
    (fun n ↦ relativeBarPairMap F (I.columnRightActionHom a n).toPairMap) (by
      intro n
      have hs : (I.relativeAffineRankSequence F).map (homOfLE (Nat.le_add_right n 1)) =
          relativeBarPairMap F (I.columnBlockOverHom n 1).toPairMap :=
        Functor.ofSequence_map_homOfLE_succ _ _
      rw [hs, ← relativeBarPairMap_comp, ← relativeBarPairMap_comp,
        I.columnRight_block_commute a n 1])

/-- 概要：有限 rank の右乗法が相対加群の実余極限に誘導する写像。
方針：実自然変換を余極限関手で写す。
規約：KST Proposition 4.14、零性を定義に入れない。
使われ方：有限 rank の Claim 4.15 からの安定零化。 -/
def NonUnitalSimplicialRing.relativeAffineRightColimitMap (I : NonUnitalSimplicialRing.{u})
    (a : I.obj (op ⦋0⦌)) (F : SSet.{u} ⥤ ModuleCat.{u} ℤ) :
    I.relativeAffineColimit F ⟶ I.relativeAffineColimit F :=
  colimMap (I.relativeAffineRightNatTrans a F)

/-- 概要：実余極限への有限 rank の脚の後の右乗法は低次で零。
方針：rank を i だけ増やし、Claim 4.15 と実余極限の脚の可換性を使う。
規約：KST Proposition 4.14、H_* の自然な複体模型を明示的に借りる。
使われ方：実余極限上の写像の外延性による零化。 -/
lemma NonUnitalSimplicialRing.relativeAffineRight_leg_zero (I : NonUnitalSimplicialRing.{u})
    (a : I.obj (op ⦋0⦌)) (F : SSet.{u} ⥤ ModuleCat.{u} ℤ)
    (hF : SSet.anodyneExtensions.IsInvertedBy F) {i : ℕ} (M : SimplicialHomologyModel F i) (n : ℕ) :
    relativeBarPairMap F (I.columnRightActionHom a n).toPairMap ≫ I.relativeAffineInclusion F n = 0 := by
  have hz : relativeBarPairMap F (I.columnRightActionHom a n).toPairMap ≫
      (I.relativeAffineRankSequence F).map (homOfLE (Nat.le_add_right n i)) = 0 := by
    rw [I.relativeAffineRankSequence_map, ← relativeBarPairMap_comp,
      I.columnRight_then_block, claim415 I a n i F hF M (le_refl i)]
  calc
    relativeBarPairMap F (I.columnRightActionHom a n).toPairMap ≫ I.relativeAffineInclusion F n =
        relativeBarPairMap F (I.columnRightActionHom a n).toPairMap ≫
          (I.relativeAffineRankSequence F).map (homOfLE (Nat.le_add_right n i)) ≫
            I.relativeAffineInclusion F (n + i) := by
      exact congrArg
        (fun t ↦ relativeBarPairMap F (I.columnRightActionHom a n).toPairMap ≫ t)
        (colimit.w (I.relativeAffineRankSequence F) (homOfLE (Nat.le_add_right n i))).symm
    _ = 0 := by rw [← Category.assoc, hz, Limits.zero_comp]

/-- 概要：相対アフィン加群の実 rank 余極限上の右乗法は低次で零。
方針：零性を含めず定義した実誘導射を各有限 rank の脚で評価して Claim 4.15 を使う。
規約：KST Proposition 4.14 の安定化の代数部分。安定 H_* との比較自体を主張しない。
使われ方：所有レーンの filtered homology 比較を介して安定相対ホモロジーへ移す。 -/
theorem NonUnitalSimplicialRing.relativeAffineRightColimitMap_zero (I : NonUnitalSimplicialRing.{u})
    (a : I.obj (op ⦋0⦌)) (F : SSet.{u} ⥤ ModuleCat.{u} ℤ)
    (hF : SSet.anodyneExtensions.IsInvertedBy F) {i : ℕ} (M : SimplicialHomologyModel F i) :
    I.relativeAffineRightColimitMap a F = 0 := by
  apply (colimit.isColimit (I.relativeAffineRankSequence F)).hom_ext
  intro n
  rw [Limits.comp_zero]
  change colimit.ι (I.relativeAffineRankSequence F) n ≫
    colimMap (I.relativeAffineRightNatTrans a F) = 0
  rw [ι_colimMap]
  exact I.relativeAffineRight_leg_zero a F hF M n

end SerrePositivity.KST.ProExcision
