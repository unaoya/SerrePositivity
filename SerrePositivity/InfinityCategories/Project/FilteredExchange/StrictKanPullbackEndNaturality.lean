module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.EquivalenceCalculus
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.FullyFaithfulCalculus
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.SimplicialHomotopyEquivalence
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.StrictKanPullbackEndComparison
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.BousfieldKan
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.BousfieldKanHomotopyInvariance
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.HomotopyCospanEndComparison
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.KanLimits
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.SectionsKan
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.WeightedFunctor
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.WeightedSections

/-!
概要：厳密な引き戻しの end 比較の自然性から、具体的な頂点比較の同値性を検出する。
方針：同じ錐の全成分を保つ自然性と end の成分ごとの同値不変性を合成する。
規約：空の fiber も許す。使われ方：実 fiber 模型と native 切断模型の比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
namespace SerrePositivity.InfinityCategories.Project.FilteredExchange
variable {L M R L' M' R' : SSet.{u}}
  (f : L ⟶ M) (g : R ⟶ M) (f' : L' ⟶ M') (g' : R' ⟶ M')
  (m : pullback f g ⟶ pullback f' g') (η : cospan f g ⟶ cospan f' g')

/-- 元の通常の錐の全成分に整合する比較は、標準 end 比較の四角形を厳密に保つ。 -/
lemma strictKanPullbackEndComparison_naturality
    (h : ∀ i, m ≫ (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.strictKanPullbackEndCone f' g').π.app i =
      (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.strictKanPullbackEndCone f g).π.app i ≫ η.app (AsSmall.down.obj i)) :
    m ≫ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.strictKanPullbackEndComparison f' g' =
      _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.strictKanPullbackEndComparison f g ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsMap _
        (Functor.whiskerLeft AsSmall.down η) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedConeComparison_naturality _
    (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.strictKanPullbackEndCone f g) (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.strictKanPullbackEndCone f' g') m
    (Functor.whiskerLeft AsSmall.down η) h

/-- 一脚 fibration の Kan cospan 間では、同じ厳密な錐比較の同値性を end で検出する。 -/
lemma strictKanPullbackEndComparison_detect_homotopyEquivalence
    [KanComplex L] [KanComplex M] [KanComplex R]
    [KanComplex L'] [KanComplex M'] [KanComplex R'] [Fibration f] [Fibration f']
    (h : ∀ i, m ≫ (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.strictKanPullbackEndCone f' g').π.app i =
      (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.strictKanPullbackEndCone f g).π.app i ≫ η.app (AsSmall.down.obj i))
    (hη : ∀ i, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (η.app i)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence m := by
  have : KanComplex (pullback f g) := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.pullback_kanComplex_of_fibration f g
  have : KanComplex (pullback f' g') :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.pullback_kanComplex_of_fibration f' g'
  have : ∀ i, KanComplex
      (((AsSmall.down : AsSmall.{u} WalkingCospan ⥤ WalkingCospan) ⋙
        cospan f g).obj i) := by
    rintro ⟨_ | ⟨_ | _⟩⟩ <;> infer_instance
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanHolim_kanComplex
    ((AsSmall.down : AsSmall.{u} WalkingCospan ⥤ WalkingCospan) ⋙ cospan f g)
  have : ∀ i, KanComplex
      (((AsSmall.down : AsSmall.{u} WalkingCospan ⥤ WalkingCospan) ⋙
        cospan f' g').obj i) := by
    rintro ⟨_ | ⟨_ | _⟩⟩ <;> infer_instance
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanHolim_kanComplex
    ((AsSmall.down : AsSmall.{u} WalkingCospan ⥤ WalkingCospan) ⋙ cospan f' g')
  apply (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.strictKanPullbackEndComparison_homotopyEquivalence f' g').cancel_right
  rw [strictKanPullbackEndComparison_naturality f g f' g' m η h]
  exact (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.strictKanPullbackEndComparison_homotopyEquivalence f g).comp
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanMap_homotopyEquivalence _ (fun i => hη (AsSmall.down.obj i)))

end SerrePositivity.InfinityCategories.Project.FilteredExchange
