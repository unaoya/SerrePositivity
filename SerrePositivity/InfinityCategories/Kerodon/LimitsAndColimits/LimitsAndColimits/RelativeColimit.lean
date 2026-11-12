module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RelativeCoconeSliceMapping
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：写像空間による相対始対象と標準的な U 余極限の定義。
方針：通常の coslice の後合成について、始点を固定した写像空間の同値を要求する。
規約：操作的な始点境界充填とは別に定義し、証明した方向だけを接続する。
使われ方：Kerodon Definitions 7.1.5.1（Tag 02KU）・7.1.6.1（Tag 02KG）、相対 Kan 条件の標準化。

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

/-- 概要：U に関する相対始対象は、その点からの全ての写像空間を U が保つ点。
方針：右 pinched 模型の比較のホモトピー同値性で定義する。
規約：quasicategory に適用したとき Kerodon Definition 7.1.5.1（Tag 02KU） の意味を持つ。
使われ方：局所余錐と大域的な関手の相対普遍性の共通の型。 -/
@[kerodon 02KU]
def KanRelativeInitialVertex {D E : SSet.{u}} (U : D ⟶ E) (x : D _⦋0⦌) : Prop :=
  ∀ y : D _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap U x y)

/-- 概要：U 余極限余錐は、通常の余錐の coslice の後合成に関する相対始対象。
方針：標準の coslice の頂点 c に相対始対象の条件を課す。
規約：Kerodon Definition 7.1.6.1（Tag 02KG） の余極限側。操作的な充填条件は定義に含めない。
使われ方：標準的な相対 Kan 拡張の局所入力。 -/
@[kerodon 02KG]
def IsRelativeColimitCone {K D E : SSet.{u}} (U : D ⟶ E) {p : K ⟶ D}
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p) : Prop :=
  KanRelativeInitialVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderPostcomp p U) c

/-- 概要：相対始点境界充填を持つ点は写像空間の意味で相対始対象。
方針：coslice の相対端点比較を介する右 pinched 模型の同値を使う。
規約：D と E は quasicategory、U に充填性を要求しない。
使われ方：厳密な構成で得た相対普遍性を標準条件へ移す。 -/
lemma kanRelativeInitialVertex_of_initialBoundary {D E : SSet.{u}}
    [Quasicategory D] [Quasicategory E] (U : D ⟶ E) (x : D _⦋0⦌)
    (hx : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.InitialBoundaryLifting U x) : KanRelativeInitialVertex U x :=
  fun y ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.pinchedHomMap_equivalence_of_initialBoundary U x y hx

/-- 概要：操作的な相対余錐の充填条件は標準の U 余極限条件を含意する。
方針：通常の coslice の写像空間の同値を各余錐について適用する。
規約：U が isofibration であることを要求しない。
使われ方：構成済みの局所余錐を標準的な相対 Kan 条件へ接続する。 -/
lemma kanIsRelativeColimitCone_of_lifting {K D E : SSet.{u}}
    [Quasicategory D] [Quasicategory E] (U : D ⟶ E) {p : K ⟶ D}
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.KanRelativeCoconeLifting U c) : IsRelativeColimitCone U c :=
  fun d ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeCoconeLifting_slice_pinchedHom_equivalence p U c hc d

/-- 概要：相対始対象性は始域と像での相対始対象性を合成して保たれる。
方針：右 pinched 比較の合成公式とホモトピー同値の合成を使う。
規約：三つの単体集合は quasicategory とする。
使われ方：相対余極限の標的変更と相対 Kan 条件の推移性。 -/
lemma KanRelativeInitialVertex.comp {D E B : SSet.{u}}
    [Quasicategory D] [Quasicategory E] [Quasicategory B] {U : D ⟶ E} {V : E ⟶ B}
    {x : D _⦋0⦌} (hx : KanRelativeInitialVertex U x)
    (hy : KanRelativeInitialVertex V (U.app (Opposite.op ⦋0⦌) x)) :
    KanRelativeInitialVertex (U ≫ V) x := by
  intro y
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap_comp]
  exact (hx y).comp (hy _)

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
