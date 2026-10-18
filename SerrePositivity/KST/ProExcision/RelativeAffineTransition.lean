module
public import SerrePositivity.KST.ProExcision.ColumnBlockPairCoherence
public import SerrePositivity.KST.ProExcision.RelativeAffineRankSequence

/-!
# 相対アフィン加群の実順序列の遷移

概要：任意の有限遷移を一度の通常のブロック安定化に同定する。
方針：実対射の恒等・合成則と相対 bar 写像の関手性を使う。
規約：KST Claim 4.15 から Proposition 4.14 の安定化。
使われ方：十分大きい rank の零化を実余極限の脚へ後合成する。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.ProExcision
open CategoryTheory

/-- 概要：恒等対射の相対 bar 写像は恒等。
方針：通常商の代表元で関手の恒等保存を計算する。
規約：KST Proposition 4.14。使われ方：rank 遷移の基底。 -/
lemma relativeBarPairMap_identity (F : SSet.{u} ⥤ ModuleCat.{u} ℤ)
    {G H : SimplicialObject MonCat.{u}} (A : SimplicialMonoidAction G H) :
    relativeBarPairMap F (SimplicialActionPairMap.identity A) = 𝟙 (relativeBarModule F A) := by
  unfold relativeBarPairMap SimplicialActionPairMap.identity
  simp only [Comparison.monoidBarMap_id, F.map_id]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  induction x using Submodule.Quotient.induction_on with
  | _ x => rfl

/-- 概要：相対アフィン加群の任意の有限 rank の遷移は通常のブロック対射の相対写像。
方針：補助 rank に関する帰納法で実対射の一座標ずつの合成則を使う。
規約：KST Claim 4.15 から Proposition 4.14 の安定化。
使われ方：有限 rank の零写像を実順序列へ移す。 -/
lemma NonUnitalSimplicialRing.relativeAffineRankSequence_map (I : NonUnitalSimplicialRing.{u})
    (F : SSet.{u} ⥤ ModuleCat.{u} ℤ) (n m : ℕ) :
    (I.relativeAffineRankSequence F).map (homOfLE (Nat.le_add_right n m)) =
      relativeBarPairMap F (I.columnBlockOverHom n m).toPairMap := by
  induction m with
  | zero =>
    rw [show homOfLE (Nat.le_add_right n 0) = 𝟙 n from Subsingleton.elim _ _,
      CategoryTheory.Functor.map_id, I.columnBlockPair_zero, relativeBarPairMap_identity]
    rfl
  | succ m ih =>
    have hs : (I.relativeAffineRankSequence F).map (homOfLE (Nat.le_add_right (n + m) 1)) =
        relativeBarPairMap F (I.columnBlockOverHom (n + m) 1).toPairMap :=
      Functor.ofSequence_map_homOfLE_succ _ _
    rw [← I.columnBlockPair_succ n m, relativeBarPairMap_comp]
    calc
      (I.relativeAffineRankSequence F).map (homOfLE (Nat.le_add_right n (m + 1))) =
          (I.relativeAffineRankSequence F).map (homOfLE (Nat.le_add_right n m)) ≫
            (I.relativeAffineRankSequence F).map (homOfLE (Nat.le_add_right (n + m) 1)) := by
        rw [← CategoryTheory.Functor.map_comp]
        congr 1
      _ = _ := by rw [ih, hs]

end SerrePositivity.KST.ProExcision
