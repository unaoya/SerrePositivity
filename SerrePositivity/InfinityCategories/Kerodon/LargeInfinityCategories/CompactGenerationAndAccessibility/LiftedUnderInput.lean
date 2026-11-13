module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.UncurriedInputRightRestriction
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.MappingSpaces.UniverseJoinNaturality

/-!
概要：指定始点の下の小図式を、小さい join を持ち上げた全入力に展開する。
方針：元の全 uncurry と実 join の宇宙同型を合成する。
規約：指定始点の形状も元の可変入力も保持する。
使われ方：成分射影の under comma で追加入力を保つ交互構成。

対応節は Kerodon 9.4（Tag 06GT）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility


/-- 概要：小さい始点形状の下の小図式を同じ小さい join の全入力にする。
方針：実際の宇宙 join 同型の後で元の coslice 図式を展開する。
規約：元の全図式から構成し、入力の存在を仮定しない。
使われ方：元の成分の追加入力付き compact 表示。 -/
def liftedUnderInputDiagram {A K : SSet.{u}} {Y : SSet.{u + 1}}
    {z : (SSet.uliftFunctor.{u + 1, u}).obj A ⟶ Y}
    (t : (SSet.uliftFunctor.{u + 1, u}).obj K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder z) :
    (SSet.uliftFunctor.{u + 1, u}).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join A K) ⟶ Y :=
  (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftJoinIso A K).hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry t

/-- 概要：展開した追加入力の右因子は元の可変図式の基底射影。
方針：宇宙 join 同型の右包含と全 uncurry の右射影を使う。
規約：元の図式の厳密な等式。
使われ方：元の成分入力への安定な制限。 -/
lemma liftedUnderInputDiagram_right {A K : SSet.{u}} {Y : SSet.{u + 1}}
    {z : (SSet.uliftFunctor.{u + 1, u}).obj A ⟶ Y}
    (t : (SSet.uliftFunctor.{u + 1, u}).obj K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder z) :
    (SSet.uliftFunctor.{u + 1, u}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr A K) ≫ liftedUnderInputDiagram t =
      t ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection z := by
  rw [liftedUnderInputDiagram, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftJoinIso_inr,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.sliceUnderUncurry_projection]

/-- 概要：展開した小さい全入力の余錐は元の指定始点の下の余錐を与える。
方針：同じ実宇宙 join 同型と反復 coslice の逆で戻す。
規約：元の可変図式の基底全余錐値を厳密に回収する。
使われ方：compact 成分の比較から under comma の全余錐へ戻す。 -/
lemma exists_liftedUnderCocone_of_inputCocone {A K : SSet.{u}} {Y : SSet.{u + 1}}
    {z : (SSet.uliftFunctor.{u + 1, u}).obj A ⟶ Y}
    (t : (SSet.uliftFunctor.{u + 1, u}).obj K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder z)
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (liftedUnderInputDiagram t)) :
    ∃ d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone t, (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection z) d).val =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap ((SSet.uliftFunctor.{u + 1, u}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr A K)) (𝟙 Δ[0]) ≫ c.val :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.exists_cosliceCocone_of_uncurriedCocone t (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftJoinIso A K)
    ((SSet.uliftFunctor.{u + 1, u}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr A K)) (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftJoinIso_inr A K) c

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility
