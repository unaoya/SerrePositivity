module

public import SerrePositivity.InfinityCategories.F1.CocartesianPullbackMarkCover
public import SerrePositivity.InfinityCategories.F1.CocartesianPullbackNativeRestriction
public import SerrePositivity.InfinityCategories.F1.MarkedCocartesianFunctorEquivalenceRestriction

/-!
概要：全辺を含む inner anodyne な底への、元の cocartesian Hom の自明 Kan 制限。
方針：元の全空間への制限を指定辺を覆う単射な同値として扱い、標的の底変換同型で移す。
規約：両射影を底変換した元の cocartesian Hom の core そのものを使う。
使われ方：高次内ホーンの付加に沿う分類主写像の Hom 比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

variable {E F B : SSet.{u}} [Quasicategory B]
variable (p : E ⟶ B) [CocartesianFibration p] (q : F ⟶ B) [CocartesianFibration q]
variable (a : Over B) (ha : innerAnodyneExtensions a.hom)
variable (he : Function.Surjective (a.hom.app (Opposite.op ⦋1⦌)))
include ha he

/-- 元の標的への cocartesian Hom の制限の core は、同じ全辺を覆う底変換で自明 Kan。 -/
lemma core_cocartesianPullbackHomRestriction_trivialKanFibration :
    TrivialKanFibration (quasicategoryCoreMap (cocartesianPullbackHomRestriction p q a)) := by
  letI : Mono a.hom := mono_of_innerAnodyne a.hom ha
  unfold cocartesianPullbackHomRestriction
  apply core_markedCocartesianFunctorPre_trivialKanFibration_of_markCover
  · exact cocartesianPullback_snd_isPrecompositionEquivalence_of_innerAnodyne p a.hom ha
  · intro e h
    obtain ⟨d, hd, hde⟩ := exists_cocartesianPullbackEdge_of_base_edgeSurjective p a he e h
    exact ⟨d, hd, hde⟩

/-- 両射影を底変換した元の cocartesian Hom の core への制限も、同じ自明 Kan fibration。 -/
lemma core_cocartesianPullbackNativeRestriction_trivialKanFibration :
    TrivialKanFibration (quasicategoryCoreMap (cocartesianPullbackNativeRestriction p q a)) := by
  letI := core_cocartesianPullbackHomRestriction_trivialKanFibration p q a ha he
  change TrivialKanFibration (quasicategoryCoreFunctor.map
    (cocartesianPullbackHomRestriction p q a ≫ (cocartesianPullbackHomIso p q a).inv))
  rw [Functor.map_comp]
  exact ⟨trivialKanFibrations.comp_mem _ _
    (core_cocartesianPullbackHomRestriction_trivialKanFibration p q a ha he).mem
    (trivialKanFibrations.of_isIso _)⟩

end SerrePositivity.InfinityCategories
