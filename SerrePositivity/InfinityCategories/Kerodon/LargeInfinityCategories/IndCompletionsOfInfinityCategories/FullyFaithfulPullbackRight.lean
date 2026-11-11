module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.PinchedHomPullbackSquare
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.PinchedHomEndpointTransport
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanFibrationEquivalenceLifting
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.EquivalenceLiftingPullback

/-!
概要：右側の射が inner fibration のとき、充満忠実性を厳密な引き戻しへ移す。
方針：元の右写像空間の pullback と、右側の全ホーンの充填性を使う。
規約：充満忠実な左側の射自身には充填性を要求しない。使われ方：実 diagram comma。

対応節は Kerodon 9.3（Tag 06FR）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories

/-- 右側が inner fibration なら、左側の充満忠実性は第二射影へ移る。 -/
lemma fullyFaithful_pullback_snd_of_innerFibration_right
    {X Y B : SSet.{u}} [Quasicategory X] [Quasicategory Y] [Quasicategory B]
    {p : X ⟶ B} (hp : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful p) (q : Y ⟶ B) [InnerFibration q] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful (pullback.snd p q) := by
  have : InnerFibration (pullback.fst p q) :=
    ⟨innerFibrations.pullback_fst p q (InnerFibration.mem (q := q))⟩
  have : Quasicategory (pullback p q) := quasicategory_of_innerFibration (pullback.fst p q)
  intro v w
  let mp := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap p ((pullback.fst p q).app (Opposite.op ⦋0⦌) v)
    ((pullback.fst p q).app (Opposite.op ⦋0⦌) w)
  let mq := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomPullbackBaseMap p q v w
  let e := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pinchedHomIsoOfEq (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pullbackSimplex_compat p q v).symm
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pullbackSimplex_compat p q w).symm
  have hm : mq = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap q ((pullback.snd p q).app (Opposite.op ⦋0⦌) v)
      ((pullback.snd p q).app (Opposite.op ⦋0⦌) w) ≫ e.hom := by
    apply SSet.hom_ext
    rintro ⟨⟨n⟩⟩
    apply ConcreteCategory.hom_ext
    intro s
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.Simplex.ext
    change _ = ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pinchedHomIsoOfEq _ _).hom.app (Opposite.op ⦋n⦌) _).val
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pinchedHomIsoOfEq_hom_val]
    rfl
  have : Fibration (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap q ((pullback.snd p q).app (Opposite.op ⦋0⦌) v)
      ((pullback.snd p q).app (Opposite.op ⦋0⦌) w)) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.fibration_of_hasLiftingProperty_horn _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomMap_hasLiftingProperty_horn q _ _)
  have : Fibration mq := by
    rw [hm]
    infer_instance
  have he : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence mp := (hp _ _).isQCatEquivalence
  have hpb := (he.pullback_snd_isPrecompositionEquivalence_of_kanEquivalenceLifting mq
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanEquivalenceLifting_of_kanFibration mq)).isQCatEquivalence
  have hs := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.pinchedHomPullback_isPullback p q v w
  have h := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso hs.isoPullback).isQCatEquivalence.comp hpb
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (hs.isoPullback.hom ≫ pullback.snd mp mq) at h
  rw [hs.isoPullback_hom_snd] at h
  exact h.isSimplicialHomotopyEquivalence

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
