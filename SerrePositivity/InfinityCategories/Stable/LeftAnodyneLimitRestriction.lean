module
public import SerrePositivity.InfinityCategories.Stable.PosetInteriorPrism
public import SerrePositivity.InfinityCategories.F2.CatInfinity.LimitConeExtension
public import SerrePositivity.InfinityCategories.Core.SliceRestriction
public import SerrePositivity.InfinityCategories.Core.EquivalenceTerminal
public import SerrePositivity.InfinityCategories.Stable.ExcisionGridCoreDiagram
public import SerrePositivity.InfinityCategories.Core.LeftPrism
public import SerrePositivity.InfinityCategories.Core.PrismFilling
public import SerrePositivity.InfinityCategories.Stable.PosetClosureRetraction

/-!
概要：比較格子の穿孔 core と元の cospan の実極限を比較する。
方針：固定した初期収縮と標準ホーンの全単体同型を使う。
規約：一般安定性を仮定しない。使われ方：HA 1.4.2.15 の実 θ の構成。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet MorphismProperty
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

lemma isLimitCone_iff_restrict_of_leftAnodyne {K L X : SSet.{u}} [Quasicategory X]
    {p : K ⟶ X} (c : JoinCone p) (i : L ⟶ K) [Mono i] (hi : leftAnodyneExtensions i) :
    IsLimitCone c ↔ IsLimitCone (F2.restrictJoinCone c i) := by
  have := sliceOverRestrict_trivialKanFibration p i hi
  exact (qCatEquivalenceOfTrivialKanFibration (sliceOverRestrict p i)).isTerminalVertex_iff c

end SerrePositivity.InfinityCategories
