module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.CosliceTrivialFibration
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RelativeInitialComparison

/-!
概要：自明 Kan fibration の前後での相対余極限の比較。
方針：coslice の後合成の充満忠実性と頂点上の全射性を使う。
規約：後合成する一般の関手には fibration 性を要求しない。
使われ方：可逆 path による因子分解で局所の相対余極限を移す。

対応節は Kerodon 7.1（Tag 02H1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits

/-- 概要：同じ図式を表す余錐の相対余極限性は表示に依存しない。
方針：底の図式の等式で置換した後、部分型の値の等式を使う。
規約：異なる固定図式の型の余錐を、その厳密な等式で比較する。
使われ方：切断と射影の合成で得た余錐を元の余錐へ戻す。 -/
lemma kanIsRelativeColimitCone_congr {K D E : SSet.{u}} (U : D ⟶ E)
    {p q : K ⟶ D} (hpq : p = q) (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p) (d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone q)
    (hcd : c.val = d.val) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsRelativeColimitCone U c ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsRelativeColimitCone U d := by
  subst q
  have h : c = d := Subtype.ext hcd
  rw [h]

/-- 概要：充満忠実な後合成は相対始対象性を検出する。
方針：各写像空間の合成から後半の同値を消去する。
規約：三つの単体集合は quasicategory。
使われ方：path の両端評価による相対普遍性の比較。 -/
lemma kanRelativeInitialVertex_comp_iff_of_fullyFaithful {X Y Z : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] [Quasicategory Z]
    (f : X ⟶ Y) (g : Y ⟶ Z) (hg : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful g) (x : X _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.KanRelativeInitialVertex (f ≫ g) x ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.KanRelativeInitialVertex f x := by
  constructor
  · intro h y
    have he := h y
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap_comp] at he
    exact (hg _ _).cancel_right he
  · intro h y
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap_comp]
    exact (h y).comp (hg _ _)

/-- 概要：頂点に全射な充満忠実比較は相対始対象性を始域で検出する。
方針：終点を持ち上げ、写像空間の合成から前半の同値を消去する。
規約：相対始点は比較射で写す。
使われ方：path 置換から元の始域への相対普遍性の移送。 -/
lemma kanRelativeInitialVertex_comp_iff_of_surjective_fullyFaithful {X Y Z : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] [Quasicategory Z]
    (f : X ⟶ Y) (g : Y ⟶ Z) (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful f)
    (hs : Function.Surjective (f.app (Opposite.op ⦋0⦌))) (x : X _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.KanRelativeInitialVertex (f ≫ g) x ↔
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.KanRelativeInitialVertex g (f.app (Opposite.op ⦋0⦌) x) := by
  constructor
  · intro h y
    obtain ⟨z, rfl⟩ := hs y
    have he := h z
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap_comp] at he
    exact (hf x z).cancel_left he
  · intro h y
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap_comp]
    exact (hf x y).comp (h _)

/-- 概要：自明 Kan fibration の後合成前後で標準の相対余極限性は同値。
方針：coslice の自明 Kan 性から充満忠実性を取り、写像空間で消去する。
規約：余錐の図式と対象は変えない。
使われ方：可逆 path の二つの端点評価の消去。 -/
lemma kanIsRelativeColimitCone_comp_iff_of_trivialKanFibration {K X Y Z : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] [Quasicategory Z]
    (f : X ⟶ Y) (g : Y ⟶ Z) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration g]
    {p : K ⟶ X} (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsRelativeColimitCone (f ≫ g) c ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsRelativeColimitCone f c := by
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.CosliceTrivialFibration.sliceUnderPostcomp_trivialKanFibration (p ≫ f) g
  exact kanRelativeInitialVertex_comp_iff_of_fullyFaithful
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderPostcomp p f) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderPostcomp (p ≫ f) g)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isQCatEquivalence_of_trivialKanFibration _).isFullyFaithful c

/-- 概要：自明 Kan fibration による余錐の像で相対余極限性を検出する。
方針：coslice の後合成の切断で頂点を持ち上げ、充満忠実な比較を消去する。
規約：余錐の像は coslice の頂点として指定する。
使われ方：path 置換の射影に沿う標準の相対余極限の移送。 -/
lemma kanIsRelativeColimitCone_precomp_iff_of_trivialKanFibration {K X Y Z : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] [Quasicategory Z]
    (f : X ⟶ Y) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration f] (g : Y ⟶ Z)
    {p : K ⟶ X} (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsRelativeColimitCone (f ≫ g) c ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsRelativeColimitCone g
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderPostcomp p f).app (Opposite.op ⦋0⦌) c) := by
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.CosliceTrivialFibration.sliceUnderPostcomp_trivialKanFibration p f
  obtain ⟨s, hs⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.trivialKanFibration_exists_section (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderPostcomp p f)
  have hsurj : Function.Surjective ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderPostcomp p f).app (Opposite.op ⦋0⦌)) := by
    intro y
    exact ⟨s.app (Opposite.op ⦋0⦌) y,
      ConcreteCategory.congr_hom (NatTrans.congr_app hs (Opposite.op ⦋0⦌)) y⟩
  exact kanRelativeInitialVertex_comp_iff_of_surjective_fullyFaithful
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderPostcomp p f) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderPostcomp (p ≫ f) g)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isQCatEquivalence_of_trivialKanFibration _).isFullyFaithful hsurj c

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
