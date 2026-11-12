module

public import SerrePositivity.KST.LocalizingInvariants.InitialConeTensorCornerGluing
public import SerrePositivity.KST.LocalizingInvariants.VerdierInitialConeTensorBoundary

/-!
概要：回収済みの元の有限図式と尾部から、全実境界と指定商図式への全比較を構成する。
方針：実 pushout で図式と比較円柱を同時に貼り、構成した全境界比較で実延長を回収する。
規約：全境界 p とその全同型 e は入力にせず、両実図式と共有する実比較から構成する。
使われ方：c5 の次元延長の貼合せ段階。任意完成族からの両実図式の回収は別途必要。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants

/-- 元の二つの実図式と共有する全比較を貼り、同じ全商図式の実拡張を得る。 -/
lemma exists_verdierInitialConeTensorGluedBoundary {A₀ B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}}
    {i : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A₀ B} {q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C} (h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence i q)
    (A L : SSet.{u}) [A.Finite] [L.Finite]
    (F : (A.op ⊗ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join L.op (Δ[0] : SSet.{u})).op ⟶ B.obj)
    (G : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join A.op (Δ[0] : SSet.{u}) ⊗ L.op).op ⟶ B.obj)
    (w : SSet.opFunctor.map (A.op ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl L.op (Δ[0] : SSet.{u})) ≫ F =
      SSet.opFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl A.op (Δ[0] : SSet.{u}) ▷ L.op) ≫ G)
    (H : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[0] : SSet.{u}) A ⊗ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[0] : SSet.{u}) L ⟶ C.obj)
    (J : SSet.Homotopy
      (initialConeTensorOldInclusion A L ≫ initialConeTensorCornerInclusion A L ≫ H)
      (F ≫ q.hom))
    (K : SSet.Homotopy
      (initialConeTensorTailInclusion A L ≫ initialConeTensorCornerInclusion A L ≫ H)
      (G ≫ q.hom))
    (hw : (SSet.opFunctor.map (A.op ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl L.op (Δ[0] : SSet.{u})) ▷ Δ[1]) ≫ J.h =
      (SSet.opFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl A.op (Δ[0] : SSet.{u}) ▷ L.op) ▷ Δ[1]) ≫ K.h)
    (hJ : ∀ x, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge J x).toTruncated)
    (hK : ∀ x, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge K x).toTruncated) :
    ∃ D : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[0] : SSet.{u}) A ⊗ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[0] : SSet.{u}) L ⟶ B.obj,
      (initialConeTensorOldInclusion A L ≫ initialConeTensorCornerInclusion A L) ≫ D = F ∧
      (initialConeTensorTailInclusion A L ≫ initialConeTensorCornerInclusion A L) ≫ D = G ∧
      Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (D ≫ q.hom) H) := by
  let p := initialConeTensorCornerGlue F G w
  have hpF : initialConeTensorOldInclusion A L ≫ (p ≫ q.hom) = F ≫ q.hom := by
    rw [← Category.assoc, initialConeTensorCornerGlue_old]
  have hpG : initialConeTensorTailInclusion A L ≫ (p ≫ q.hom) = G ≫ q.hom := by
    rw [← Category.assoc, initialConeTensorCornerGlue_tail]
  let J' : SSet.Homotopy
      (initialConeTensorOldInclusion A L ≫ (initialConeTensorCornerInclusion A L ≫ H))
      (initialConeTensorOldInclusion A L ≫ (p ≫ q.hom)) := {
    h := J.h
    h₀ := J.h₀
    h₁ := J.h₁.trans hpF.symm
    rel := J.rel }
  let K' : SSet.Homotopy
      (initialConeTensorTailInclusion A L ≫ (initialConeTensorCornerInclusion A L ≫ H))
      (initialConeTensorTailInclusion A L ≫ (p ≫ q.hom)) := {
    h := K.h
    h₀ := K.h₀
    h₁ := K.h₁.trans hpG.symm
    rel := K.rel }
  have hiJ : ∀ x, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge J' x).toTruncated := by
    intro x
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr (e := (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge J' x).toTruncated)
      (f := (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge J x).toTruncated) rfl).mpr (hJ x)
  have hiK : ∀ x, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge K' x).toTruncated := by
    intro x
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr (e := (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge K' x).toTruncated)
      (f := (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge K x).toTruncated) rfl).mpr (hK x)
  let U := pushoutComparisonHomotopy (initialConeTensorCorner_isPushout A L) J' K' hw
  have hi : IsIso (Truncated.HomotopyCategory.homMk
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy U)) :=
    pushoutComparisonHomotopy_isInvertible (initialConeTensorCorner_isPushout A L)
      J' K' hw hiJ hiK
  let e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (initialConeTensorCornerInclusion A L ≫ H) (p ≫ q.hom) :=
    asIso (Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy U))
  obtain ⟨d⟩ := exists_verdierInitialConeTensorBoundary h A L p H e
  refine ⟨d.diagram, ?_, ?_, ⟨d.iso⟩⟩
  · rw [Category.assoc, d.boundary]
    exact initialConeTensorCornerGlue_old F G w
  · rw [Category.assoc, d.boundary]
    exact initialConeTensorCornerGlue_tail F G w

end SerrePositivity.KST.LocalizingInvariants
