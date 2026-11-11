module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.FullyFaithfulBaseChange

/-!
概要：元の引き戻しの右写像空間を、元の両射影の厳密な pullback として読む。
方針：既存の全 pinched 単体の持ち上げと両射影による一意性を束ねる。
規約：元の頂点と射を保持。使われ方：Yoneda の充填性を仮定しない comma 比較。

対応節は Kerodon 9.3（Tag 06FR）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
variable {X Y B : SSet.{u}} (p : X ⟶ B) (q : Y ⟶ B)
  (v w : (pullback p q) _⦋0⦌)

/-- 同じ元の両射影による右写像空間の四角形は、厳密な pullback。 -/
lemma pinchedHomPullback_isPullback :
    IsPullback (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap (pullback.fst p q) v w)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap (pullback.snd p q) v w)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap p ((pullback.fst p q).app (Opposite.op ⦋0⦌) v)
        ((pullback.fst p q).app (Opposite.op ⦋0⦌) w))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomPullbackBaseMap p q v w) := by
  refine IsPullback.mk' (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomPullbackBaseMap_comm p q v w) ?_ ?_
  · intro T f g hf hg
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomPullback_hom_ext p q v w hf hg
  · intro T f g h
    have hc (n : ℕ) (t : T _⦋n⦌) :
        p.app (Opposite.op ⦋n + 1⦌) (f.app (Opposite.op ⦋n⦌) t).val =
          q.app (Opposite.op ⦋n + 1⦌) (g.app (Opposite.op ⦋n⦌) t).val := by
      exact congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.Simplex.val
        (ConcreteCategory.congr_hom (NatTrans.congr_app h (Opposite.op ⦋n⦌)) t)
    exact ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomPullbackLift p q v w f g hc,
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomPullbackLift_fst p q v w f g hc,
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomPullbackLift_snd p q v w f g hc⟩

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
