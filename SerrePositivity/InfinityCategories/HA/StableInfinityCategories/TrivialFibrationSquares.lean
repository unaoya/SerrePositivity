module
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.TrivialFibrationCocone
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.ExactFunctor

/-! # 自明 Kan fibration による零対象と普遍四角形の比較

概要：零対象・引き戻し・押し出しを保存し反映し、完全関手を与える。
方針：始終対象と錐・余錐の保存反映を実際の四角形に適用する。
規約：安定性を事前に仮定しない。使われ方：β3 の dg nerve の安定性の輸送。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories
open CategoryTheory MonoidalCategory SSet
open scoped _root_.Simplicial
variable {E B : SSet.{u}} [Quasicategory E] [Quasicategory B]
variable (q : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration q]

/-- 自明 Kan fibration は零対象性を保存し反映する。 -/
lemma isZeroVertex_iff_map_of_trivialKanFibration (x : E _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex x ↔ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex (q.app (Opposite.op ⦋0⦌) x) :=
  and_congr ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.qCatEquivalenceOfTrivialKanFibration q).isInitialVertex_iff x)
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.qCatEquivalenceOfTrivialKanFibration q).isTerminalVertex_iff x)

/-- 自明 Kan fibration は引き戻し四角形を保存し反映する。 -/
lemma isPullbackSquare_iff_postcomp_trivialKanFibration (F : Δ[1] ⊗ Δ[1] ⟶ E) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare F ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare (F ≫ q) := by
  simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCone, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCone, Category.assoc] using
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.isLimitCone_iff_mapJoinCone_of_trivialKanFibration q (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCone F))

/-- 自明 Kan fibration は押し出し四角形を保存し反映する。 -/
lemma isPushoutSquare_iff_postcomp_trivialKanFibration (F : Δ[1] ⊗ Δ[1] ⟶ E) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare F ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare (F ≫ q) := by
  simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutCocone, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone, Category.assoc] using
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.isColimitCone_iff_mapJoinCocone_of_trivialKanFibration q (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutCocone F))

/-- 自明 Kan fibration は零頂点を保存する。 -/
lemma trivialKanFibration_preservesZeroVertices : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.PreservesZeroVertices q :=
  fun x hx => (isZeroVertex_iff_map_of_trivialKanFibration q x).1 hx

/-- 自明 Kan fibration は安定性の事前仮定なしに完全関手である。 -/
instance isExactFunctor_of_trivialKanFibration : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor q where
  preservesZero := trivialKanFibration_preservesZeroVertices q
  preservesCofiber t ht :=
    (isPushoutSquare_iff_postcomp_trivialKanFibration q t.square).1 ht

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
