module
public import SerrePositivity.KST.Fibration.Relative.ClosedTailPullback
public import SerrePositivity.KST.Fibration.Relative.StableTrivialPullback

/-!
概要：P 相対有限旗の最後の cofiber の全補完。
方針：指定辺射影の実基底変換を使い、元の共有端点引き戻しと合成する。
規約：P の核表示を要求しない。使われ方：相対加法性の有限旗への接続。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.LocalizingInvariants
open SerrePositivity.KST.SConstruction
open SerrePositivity.SimplicialModel
namespace SerrePositivity.KST.Fibration.Relative

/-- 概要：元の長い旗と tail の完全な同値。
方針：同じ trivial Kan 制限を使う。規約：全単体。
使われ方：有限旗の元の実現との比較。 -/
def closedFlagTailEquivalence {B : StableModel.{u}} (P : ClosedStablePredicate B) (n : ℕ) :
    StableModelEquivalence (closedFlagModel P ⦋n + 2⦌) (closedTailModel P n) :=
  stableTrivialEquivalence (closedFlagTailRestriction P n)

/-- 概要：元の辺への射影とする完全な補完射。
方針：全相対 cofiber 射影の同値の順射。
規約：底辺そのもの。使われ方：全補完の基底変換。 -/
def closedCofiberProjectionExact {B : StableModel.{u}} (P : ClosedStablePredicate B) :
    relativeCofiberStableModel (ClosedStablePredicate.top B) P ⟶ closedArrowModel P :=
  (closedArrowCofiberEquivalence P).hom

/-- 概要：同じ完全射の全境界持ち上げ。
方針：元の射影と定義上一致。規約：追加仮定なし。
使われ方：実引き戻し模型の安定性。 -/
instance closedCofiberProjectionExact_trivialKan {B : StableModel.{u}}
    (P : ClosedStablePredicate B) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (closedCofiberProjectionExact P).val :=
  inferInstanceAs (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (closedCofiberProjection P))

/-- 概要：元の cofiber 射影の始点は相対 subobject。
方針：底辺の始点評価を元の四角形の評価へ戻す。
規約：全頂点部分圏値の厳密等式。使われ方：引き戻しの貼り合わせ。 -/
lemma closedCofiberProjection_source {B : StableModel.{u}} (P : ClosedStablePredicate B) :
    closedCofiberProjectionExact P ≫ closedArrowSource P =
      relativeCofiberSubobject (ClosedStablePredicate.top B) P := by
  apply Subtype.ext
  apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices B.carrier
    (ClosedStablePredicate.top B).predicate).ι).1
  change closedCofiberProjection P ≫
    (((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ (closedArrowPredicate P).predicate).ι ≫
      (pre (stdSimplex.δ (1 : Fin 2))).app B.carrier) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 1))) =
    (relativeCofiberInclusion (ClosedStablePredicate.top B) P).val ≫
      (cofiberStableSubobject B).val
  have hi : closedCofiberProjection P ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices ((ihom (Δ[1] : SSet.{u})).obj B.carrier)
        (closedArrowPredicate P).predicate).ι =
      (relativeCofiberInclusion (ClosedStablePredicate.top B) P).val ≫
        cofiberProjection B.carrier := fullPredicateMap_ι _ _ _ _
  rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.stable_pre_evaluateFunctorAt, ← Category.assoc]
  have he := congrArg (fun f => f ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2))) hi
  exact he.trans (Category.assoc _ _ _)

/-- 概要：最後の辺の全相対 cofiber 補完の安定模型。
方針：元の射影に沿う実引き戻し。
規約：全補完を保持。使われ方：最後の加法性の総空間。 -/
def closedTailCompletion {B : StableModel.{u}} (P : ClosedStablePredicate B) (n : ℕ) :
    StableModel.{u} := stableTrivialPullback (closedCofiberProjectionExact P) (closedTailEdge P n)

/-- 概要：補完から元の先行旗への射影。
方針：補完忘却と先行旗制限を合成。
規約：元の旗を回収。使われ方：加法性の第一成分。 -/
def closedTailCompletionPrefix {B : StableModel.{u}} (P : ClosedStablePredicate B) (n : ℕ) :
    closedTailCompletion P n ⟶ closedFlagModel P ⦋n + 1⦌ :=
  stableTrivialPullbackSnd (closedCofiberProjectionExact P) (closedTailEdge P n) ≫
    closedTailPrefix P n

/-- 概要：元の相対 cofiber と先行旗の共有端点引き戻し。
方針：二つの実引き戻しを貼り、始点等式を用いる。
規約：局所化前の元の四角形。使われ方：RelativePullback への入力。 -/
theorem closedTailCompletion_isPullback {B : StableModel.{u}}
    (P : ClosedStablePredicate B) (n : ℕ) :
    IsPullback
      (stableTrivialPullbackFst (closedCofiberProjectionExact P) (closedTailEdge P n)).val
      (closedTailCompletionPrefix P n).val
      (relativeCofiberSubobject (ClosedStablePredicate.top B) P).val
      (closedTailEndpoint P n).val := by
  have h := (IsPullback.of_hasPullback (closedCofiberProjectionExact P).val
    (closedTailEdge P n).val).flip.paste_horiz (closedTail_top_isPullback P n)
  have h' := h.flip
  change IsPullback _ _ (closedCofiberProjectionExact P ≫ closedArrowSource P).val _ at h'
  rw [closedCofiberProjection_source] at h'
  exact h'

/-- 概要：先行旗と最後の辺は零対象と実押し出しを共同で反映。
方針：標準 tail の全頂点被覆と完全な全部分圏への制限。
規約：全単体上の普遍性。使われ方：全 S_n の共同反映。 -/
lemma closedTail_jointReflection {B : StableModel.{u}} (P : ClosedStablePredicate B) (n : ℕ) :
    JointlyReflectsSData (closedTailPrefix P n).val (closedTailEdge P n).val := by
  exact (reindex_jointReflection (standardTailPrefix n)
    (tailAttachmentEdge (Δ[n] : SSet.{u})) (standardTail_vertex_cover n) B).fullSubcomplex
      (closedTailPredicate P n).predicate (closedFlagStablePredicate P ⦋n + 1⦌).predicate
      (closedArrowPredicate P).predicate
      (p' := (closedTailPrefix P n).val) (q' := (closedTailEdge P n).val) rfl rfl
      (stableModelHom_preservesSConstructionData
        (closedStableInclusion (closedFlagStablePredicate P ⦋n + 1⦌)))
      (stableModelHom_preservesSConstructionData (closedStableInclusion (closedArrowPredicate P)))

/-- 概要：相対加法性に渡す元の有限旗引き戻しデータ。
方針：全補完の実四角形と共同反映を組み合わせる。
規約：B と P 以外の入力なし。使われ方：加法性の全反復適用。 -/
def closedTailRelativePullback {B : StableModel.{u}} (P : ClosedStablePredicate B) (n : ℕ) :
    RelativePullback B (ClosedStablePredicate.top B) P where
  total := closedTailCompletion P n
  base := closedFlagModel P ⦋n + 1⦌
  cofiber := stableTrivialPullbackFst (closedCofiberProjectionExact P) (closedTailEdge P n)
  projection := closedTailCompletionPrefix P n
  endpoint := closedTailEndpoint P n
  isPullback := closedTailCompletion_isPullback P n
  reflects := stableTrivialPullback_jointReflection (closedCofiberProjectionExact P)
    (closedTailEdge P n) (closedTailPrefix P n) (closedTail_jointReflection P n)

/-- 概要：元の先行旗と最後の P cofiber の相対加法性。
方針：RelativePullback の既証の単回実現定理を消費。
規約：元の二成分を保持。使われ方：有限旗帰納の一段。 -/
theorem closedTailPair_localized_isIso {B : StableModel.{u}}
    (P : ClosedStablePredicate B) (n : ℕ) :
    IsIso (AnodyneHomotopy.anodyneQ.map
      ((closedTailRelativePullback P n).pair (multiRealizationFunctor 1))) :=
  (closedTailRelativePullback P n).singlePair_localized_isIso

/-- 概要：最後の相対加法性の全正有限反復。
方針：同じ実引き戻しに既存の全反復定理を適用。
規約：全次数で同じ二成分。使われ方：有限旗比較の帰納入力。 -/
theorem closedTailPair_multi_localized_isIso {B : StableModel.{u}}
    (P : ClosedStablePredicate B) (n r : ℕ) :
    IsIso (AnodyneHomotopy.anodyneQ.map
      ((closedTailRelativePullback P n).pair (multiRealizationFunctor (r + 1)))) :=
  (closedTailRelativePullback P n).multiPair_localized_isIso r

end SerrePositivity.KST.Fibration.Relative
