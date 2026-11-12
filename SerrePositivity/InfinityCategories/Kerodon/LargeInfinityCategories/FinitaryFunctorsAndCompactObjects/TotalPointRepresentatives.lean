module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.WeakComponents
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.CoherentTotalObject
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.CoherentFilteredTotalDetection

/-!
概要：元の全空間 Kan 模型の点を、元の一つの図式の値の点で連結成分まで回収する。
方針：同じ Kan 置換単位の π₀ 全射性と、元の小さい fiber の値との実同値を使う。
規約：底の filtered 性・quasicategory 性は不要。元の同じ値からの比較射を保持する。
使われ方：compact 対象の恒等射を、元の表現可能生成表示の一項へ因子化する。

対応節は Kerodon 9.2（Tag 0639）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects

/-- 元の全空間の Kan 模型の任意の点は、同じ図式の一つの値から成分まで回収できる。 -/
lemma coherentTotalKan_point_representative {B : SSet.{u}}
    (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})
    (x : _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentDiagramTotalKan F _⦋0⦌) :
    ∃ b : B _⦋0⦌,
      ∃ v : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.spaceInfinityObject (F.app (Opposite.op ⦋0⦌) (ULift.up b))).obj _⦋0⦌,
        SSet.π₀.mk ((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.coherentDiagramValueToTotalKan F b).app (Opposite.op ⦋0⦌) v) =
          SSet.π₀.mk x := by
  let E := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraightening F
  let p := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraighteningProjection F
  let η := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app E
  obtain ⟨z, hz⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.weakHomotopyEquivalence_mapPiZero_surjective η
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.continuousKanReplacementUnit_isWeakHomotopyEquivalence E) (SSet.π₀.mk x)
  obtain ⟨e, rfl⟩ := SSet.π₀.mk_surjective z
  rw [SSet.mapπ₀_mk] at hz
  let b := p.app (Opposite.op ⦋0⦌) e
  let v : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p b _⦋0⦌ := ⟨e, by rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero]⟩
  let q := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraighteningFiberValueEquivalence F b
  let w := q.hom.app (Opposite.op ⦋0⦌) v
  have H := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp q.homInvIso.simplicialHomotopy
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p b ≫ η)
  have h := SSet.π₀.sound (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge H v)
  change SSet.π₀.mk ((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.coherentDiagramValueToTotalKan F b).app (Opposite.op ⦋0⦌) w) =
    SSet.π₀.mk (η.app (Opposite.op ⦋0⦌) e) at h
  exact ⟨b, w, h.trans hz⟩

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects
