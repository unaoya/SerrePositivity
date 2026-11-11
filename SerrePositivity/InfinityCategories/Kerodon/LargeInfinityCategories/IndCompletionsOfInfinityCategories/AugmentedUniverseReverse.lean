module

public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.UniverseJoinAugmentation
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.JoinReverseCuts
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.JoinReverseEquiv
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.OppositeKanHomotopy

/-!
概要：空次数を補った単体の宇宙移送を、次数の移送と反転に両立させる。
方針：次数の等式は帰納法、反転は零次数と正次数の定義で計算する。
規約：元の単体を保持。使われ方：反転全錐と宇宙持ち上げの全射の照合。

対応節は Kerodon 9.3（Tag 06FR）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories


/-- 宇宙の上げ操作は頂点数の等式による移送と可換。 -/
lemma augmentedUniverseUp_cast (K : SSet.{u}) {r s : ℕ} (h : r = s)
    (x : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augObj K r) :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftJoinAugUp.{u, v} K s (cast (congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augObj K) h) x) =
      cast (congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augObj ((SSet.uliftFunctor.{v, u}).obj K)) h)
        (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftJoinAugUp K r x) := by
  cases h
  rfl

/-- 宇宙の下げ操作も頂点数の等式による移送と可換。 -/
lemma augmentedUniverseDown_cast (K : SSet.{u}) {r s : ℕ} (h : r = s)
    (x : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augObj ((SSet.uliftFunctor.{v, u}).obj K) r) :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftJoinAugDown K s
        (cast (congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augObj ((SSet.uliftFunctor.{v, u}).obj K)) h) x) =
      cast (congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augObj K) h) (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftJoinAugDown K r x) := by
  cases h
  rfl

/-- 反転の宇宙比較を通った単体の反転解除は元の持ち上げに等しい。 -/
lemma augmentedUniverseUp_op (K : SSet.{u}) (r : ℕ) (x : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augObj K.op r) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.stableAugOpEquiv ((SSet.uliftFunctor.{v, u}).obj K) r
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augHom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.uliftOppositeIso K).hom r (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftJoinAugUp K.op r x)) =
        _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftJoinAugUp K r (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.stableAugOpEquiv K r x) := by
  cases r <;> rfl

/-- join の切断表示の順反転は、両因子の持ち上げと反転比較に両立する。 -/
lemma augmentedReversePairUp (K L : SSet.{u}) (r : ℕ) (s : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.StableAugJoin K L r) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.stableAugJoinReversePairEquiv ((SSet.uliftFunctor.{v, u}).obj K)
      ((SSet.uliftFunctor.{v, u}).obj L) r
        ⟨s.1, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftJoinAugUp K _ s.2.1, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftJoinAugUp L _ s.2.2⟩ =
      ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.stableComplementCutEquiv r s.1,
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augHom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.uliftOppositeIso L).hom _
          (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftJoinAugUp L.op _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.stableAugJoinReversePairEquiv K L r s).2.1),
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augHom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.uliftOppositeIso K).hom _
          (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftJoinAugUp K.op _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.stableAugJoinReversePairEquiv K L r s).2.2)⟩ := by
  have hc : s.1.val = r - (r - s.1.val) := by have := s.1.isLt; omega
  refine _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.stableAugJoin_ext _ _ ?_ ?_ ?_
  · rfl
  · dsimp only [cast_eq]
    apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.stableAugOpEquiv ((SSet.uliftFunctor.{v, u}).obj L) _).injective
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.stableAugJoinReversePair_left ((SSet.uliftFunctor.{v, u}).obj K)
      ((SSet.uliftFunctor.{v, u}).obj L) r
      ⟨s.1, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftJoinAugUp K _ s.2.1, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftJoinAugUp L _ s.2.2⟩).trans
      ((augmentedUniverseUp_op L _ _).trans
        (congrArg (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftJoinAugUp L _) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.stableAugJoinReversePair_left K L r s))).symm
  · dsimp only [cast_eq]
    apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.stableAugOpEquiv ((SSet.uliftFunctor.{v, u}).obj K) _).injective
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.stableAugJoinReversePair_right ((SSet.uliftFunctor.{v, u}).obj K)
      ((SSet.uliftFunctor.{v, u}).obj L) r
      ⟨s.1, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftJoinAugUp K _ s.2.1, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftJoinAugUp L _ s.2.2⟩).trans
      ((augmentedUniverseUp_cast K hc s.2.1).symm.trans
        ((congrArg (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftJoinAugUp K _) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.stableAugJoinReversePair_right K L r s)).symm.trans
          (augmentedUniverseUp_op K _ _).symm))

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
