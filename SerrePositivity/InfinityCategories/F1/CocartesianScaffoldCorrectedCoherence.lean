module

public import SerrePositivity.InfinityCategories.F1.CocartesianScaffoldCorrectedSquares
public import SerrePositivity.InfinityCategories.F1.PathCorrectedSquareExactIso

/-!
概要：局所 cospan の補正成分の同型は、元の両脚の自然性と同じ coherence を持つ。
方針：持ち上げた同じ path の辺の類を、元の標的制限へ後合成する。
規約：共有頂点の表示変更を明示し、元の自然性の同型自体を回収する。
使われ方：元の分類作用からの二つの成分 path の共有頂点での照合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories

variable (n : ℕ) {C : Type u} [Category.{u} C] (k : ULift.{u} (Fin (n + 2)) ⥤ C)
  (p q : CocartesianFibrationCategory (nerve C))

/-- 最初の補正成分の同じ path の同型は、元の最初の脚の自然性を回収する。 -/
lemma cocartesianScaffoldCorrectedFirstSquare_coherence :
    (cocartesianScaffoldCorrectedFirstSquare n k p q).exactComponentIso.postcomp
        ((cocartesianScaffoldLocalTarget n k p q).map WalkingCospan.Hom.inl) =
      eqToIso (congrArg (fun v ↦ SSet.HomotopyCategory.mk (functorVertex v))
        (cocartesianScaffoldCorrectedFirstSquare n k p q).comm) ≪≫
          cocartesianScaffoldLocalComparison_firstIso n k p q :=
  (cocartesianScaffoldCorrectedFirstSquare n k p q).exactComponentIso_postcomp

/-- 次の補正成分でも、同じ共有頂点における元の自然性の同型を回収する。 -/
lemma cocartesianScaffoldCorrectedSecondSquare_coherence :
    (cocartesianScaffoldCorrectedSecondSquare n k p q).exactComponentIso.postcomp
        ((cocartesianScaffoldLocalTarget n k p q).map WalkingCospan.Hom.inr) =
      eqToIso (congrArg (fun v ↦ SSet.HomotopyCategory.mk (functorVertex v))
        (cocartesianScaffoldCorrectedSecondSquare n k p q).comm) ≪≫
          cocartesianScaffoldLocalComparison_secondIso n k p q :=
  (cocartesianScaffoldCorrectedSecondSquare n k p q).exactComponentIso_postcomp

end SerrePositivity.InfinityCategories
