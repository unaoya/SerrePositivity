module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.SliceTrivialFibration
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.RelativeColimitTrivialComparison
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RelativeRightCanonical
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.OppositeLifting

/-!
概要：自明 Kan fibration の前後での標準相対極限の比較。
方針：反転後の相対始対象性の消去則と slice の後合成の自明 Kan 性を使う。
規約：相対極限の対象となる一般の射に充填性は要求しない。
使われ方：一般 U の path 置換で右 Kan 条件を移す。

対応節は Kerodon 7.3（Tag 02Y1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions

/-- 概要：充満忠実な inner 後合成は相対終対象性を検出する。
方針：反転して相対始対象性の後合成の消去則を使う。
規約：三つの全空間は quasicategory。
使われ方：path の両端評価の交換。 -/
lemma kanRelativeTerminalVertex_comp_iff_of_fullyFaithful {X Y Z : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] [Quasicategory Z]
    (f : X ⟶ Y) (g : Y ⟶ Z) [InnerFibration g] (hg : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful g)
    (x : X _⦋0⦌) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.KanRelativeTerminalVertex (f ≫ g) x ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.KanRelativeTerminalVertex f x := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.KanRelativeInitialVertex (SSet.opFunctor.map (f ≫ g)) (SSet.opObjEquiv.symm x) ↔ _
  rw [Functor.map_comp]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.kanRelativeInitialVertex_comp_iff_of_fullyFaithful _ _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isFullyFaithful_op g hg) _

/-- 概要：頂点全射な充満忠実 inner 前合成は相対終対象性を検出する。
方針：反転した比較の全射性を明示し、相対始対象性の消去則を使う。
規約：相対終点は比較射の像へ移す。
使われ方：path 置換の射影による局所相対極限の判定。 -/
lemma kanRelativeTerminalVertex_comp_iff_of_surjective_fullyFaithful {X Y Z : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] [Quasicategory Z]
    (f : X ⟶ Y) (g : Y ⟶ Z) [InnerFibration f] (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful f)
    (hs : Function.Surjective (f.app (Opposite.op ⦋0⦌))) (x : X _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.KanRelativeTerminalVertex (f ≫ g) x ↔
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.KanRelativeTerminalVertex g (f.app (Opposite.op ⦋0⦌) x) := by
  have hop : Function.Surjective ((SSet.opFunctor.map f).app (Opposite.op ⦋0⦌)) := by
    intro y
    obtain ⟨z, hz⟩ := hs (SSet.opObjEquiv y)
    exact ⟨SSet.opObjEquiv.symm z, congrArg SSet.opObjEquiv.symm hz⟩
  change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.KanRelativeInitialVertex (SSet.opFunctor.map (f ≫ g)) (SSet.opObjEquiv.symm x) ↔ _
  rw [Functor.map_comp]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.kanRelativeInitialVertex_comp_iff_of_surjective_fullyFaithful _ _
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isFullyFaithful_op f hf) hop _

/-- 概要：自明 Kan 後合成の前後で標準相対極限性は同値。
方針：slice の後合成の充満忠実性を相対終対象性で消去する。
規約：元の錐は変えない。
使われ方：可逆 path の端点評価の交換。 -/
lemma kanIsRelativeLimitCone_comp_iff_of_trivialKanFibration {K X Y Z : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] [Quasicategory Z]
    (f : X ⟶ Y) (g : Y ⟶ Z) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration g]
    {p : K ⟶ X} (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsRelativeLimitCone (f ≫ g) c ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsRelativeLimitCone f c := by
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverPostcomp_trivialKanFibration (p ≫ f) g
  exact kanRelativeTerminalVertex_comp_iff_of_fullyFaithful
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverPostcomp p f) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverPostcomp (p ≫ f) g)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isQCatEquivalence_of_trivialKanFibration _).isFullyFaithful c

/-- 概要：自明 Kan fibration による錐の像で標準相対極限性を検出できる。
方針：slice の後合成の切断による頂点全射性と充満忠実性を消去する。
規約：像の錐は全体の射として指定する。
使われ方：一般 U の path 置換から元の標準局所極限へ戻す。 -/
lemma kanIsRelativeLimitCone_precomp_iff_of_trivialKanFibration {K X Y Z : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] [Quasicategory Z]
    (f : X ⟶ Y) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration f] (g : Y ⟶ Z)
    {p : K ⟶ X} (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsRelativeLimitCone (f ≫ g) c ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsRelativeLimitCone g
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverPostcomp p f).app (Opposite.op ⦋0⦌) c) := by
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverPostcomp_trivialKanFibration p f
  obtain ⟨s, hs⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.trivialKanFibration_exists_section (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverPostcomp p f)
  have hsurj : Function.Surjective ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverPostcomp p f).app (Opposite.op ⦋0⦌)) := by
    intro y
    exact ⟨s.app (Opposite.op ⦋0⦌) y,
      ConcreteCategory.congr_hom (NatTrans.congr_app hs (Opposite.op ⦋0⦌)) y⟩
  exact kanRelativeTerminalVertex_comp_iff_of_surjective_fullyFaithful
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverPostcomp p f) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverPostcomp (p ≫ f) g)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isQCatEquivalence_of_trivialKanFibration _).isFullyFaithful hsurj c

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions
