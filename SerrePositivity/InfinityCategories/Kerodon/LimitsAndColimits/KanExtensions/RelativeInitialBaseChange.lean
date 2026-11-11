module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.RelativeColimit
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.FullyFaithfulBaseChange

/-!
概要：inner fibration に関する相対始対象性の底変換。
方針：指定始点からの写像空間の比較だけを用い、引き戻しの比較の境界を充填する。
規約：元の射全体の充満忠実性は仮定しない。
使われ方：標準の相対始対象性を厳密な始点境界充填へ戻すための標準単体への還元。

対応節は Kerodon 7.3（Tag 02Y1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions

/-- 概要：相対始対象の底変換の指定始点からの写像空間の射は自明 Kan fibration。
方針：元の指定始点からの比較を充填し、指定された第二成分と引き戻しへ合わせる。
規約：底変換の始域に quasicategory 性は不要。
使われ方：相対始対象性を標準単体上の引き戻しに移す。 -/
lemma kanRelativeInitial_pinchedHom_pullback_trivialKanFibration {X Y B : SSet.{u}}
    [Quasicategory X] [Quasicategory B] (p : X ⟶ B) [InnerFibration p]
    (q : Y ⟶ B) (v : (pullback p q) _⦋0⦌)
    (hv : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.KanRelativeInitialVertex p ((pullback.fst p q).app (Opposite.op ⦋0⦌) v))
    (w : (pullback p q) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap (pullback.snd p q) v w) := by
  let mx := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap (pullback.fst p q) v w
  let my := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap (pullback.snd p q) v w
  let mp := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap p ((pullback.fst p q).app (Opposite.op ⦋0⦌) v)
    ((pullback.fst p q).app (Opposite.op ⦋0⦌) w)
  let mq := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomPullbackBaseMap p q v w
  have hm : mx ≫ mp = my ≫ mq := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomPullbackBaseMap_comm p q v w
  have : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration mp :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.trivialKanFibration_of_fibration_of_simplicialHomotopyEquivalence _ (hv _)
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.trivialKanFibration_iff_boundary _).2
  intro n
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration.mem (p := mp) (boundary n).ι inferInstance
  constructor
  intro a b sq
  have hw : (a ≫ mx) ≫ mp = (boundary n).ι ≫ (b ≫ mq) := by
    rw [Category.assoc, hm, ← Category.assoc a my mq, sq.w, Category.assoc]
  let t : CommSq (a ≫ mx) (boundary n).ι mp (b ≫ mq) := ⟨hw⟩
  have hc : ∀ (d : ℕ) (z : (Δ[n] : SSet.{u}) _⦋d⦌),
      p.app (Opposite.op ⦋d + 1⦌) (t.lift.app (Opposite.op ⦋d⦌) z).val =
        q.app (Opposite.op ⦋d + 1⦌) (b.app (Opposite.op ⦋d⦌) z).val := by
    intro d z
    exact congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.Simplex.val
      (ConcreteCategory.congr_hom (NatTrans.congr_app t.fac_right (Opposite.op ⦋d⦌)) z)
  let l := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomPullbackLift p q v w t.lift b hc
  have hmx : l ≫ mx = t.lift := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomPullbackLift_fst _ _ _ _ _ _ _
  have hmy : l ≫ my = b := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomPullbackLift_snd _ _ _ _ _ _ _
  refine CommSq.HasLift.mk' { l := l, fac_left := ?_, fac_right := hmy }
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomPullback_hom_ext p q v w
  · rw [Category.assoc, hmx]
    exact t.fac_left
  · rw [Category.assoc, hmy]
    exact sq.w.symm

/-- 概要：inner fibration の相対始対象性は quasicategory による底変換で保たれる。
方針：指定始点からの写像空間の射の自明 Kan 性をホモトピー同値へ移す。
規約：始点は引き戻しの第一成分で指定する。
使われ方：標準単体への還元と相対始対象の境界充填判定。 -/
lemma KanRelativeInitialVertex.pullback_snd {X Y B : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] [Quasicategory B]
    (p : X ⟶ B) [InnerFibration p] (q : Y ⟶ B) (v : (pullback p q) _⦋0⦌)
    (hv : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.KanRelativeInitialVertex p ((pullback.fst p q).app (Opposite.op ⦋0⦌) v)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.KanRelativeInitialVertex (pullback.snd p q) v := by
  intro w
  have := kanRelativeInitial_pinchedHom_pullback_trivialKanFibration p q v hv w
  have : InnerFibration (pullback.snd p q) :=
    ⟨innerFibrations.pullback_snd p q (InnerFibration.mem (q := p))⟩
  have : Quasicategory (pullback p q) := quasicategory_of_innerFibration (pullback.snd p q)
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isQCatEquivalence_of_trivialKanFibration _).isSimplicialHomotopyEquivalence

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.KanRelativeInitialVertex export _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.KanRelativeInitialVertex (pullback_snd)


end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions
