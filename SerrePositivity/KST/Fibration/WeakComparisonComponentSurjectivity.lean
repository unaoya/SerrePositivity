module
public import SerrePositivity.KST.Fibration.UnstraighteningComponentSurjectivity
public import SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.WeakCosliceComparisonFiberSection
public import SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.WeakNativeComponentRestriction
public import SerrePositivity.InfinityCategories.F1.Transport.FunctorIsoComponentLaws
public import SerrePositivity.KST.Fibration.KanPointSurjectivity

/-! # 元の K-6 比較二胞体と strict Kan 成分の、全ての点の射に対する全射性

既存の実右逆・相対余単位を、同じ比較の実成分へ移す。
一般分数比較の同値性・充満忠実性は未主張。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration
variable {A B C : StableCategory.{u}} {i : ExactMap A B} {q : ExactMap B C}
  (h : IsVerdierSequence i q) (x : B.obj _⦋0⦌)

/-- 同じ coslice 比較二胞体の各成分は、一点空間からの全ての射の類を覆う。 -/
theorem weakQuotientCosliceComparisonHom_point_surjective (y : C.obj _⦋0⦌) :
    Function.Surjective (fun f : HomotopyCategory.mk pointSpaceVertex ⟶
        HomotopyCategory.mk ((weakSpanKanQuotientDiagram h x).app
          (Opposite.op ⦋0⦌) (ULift.up y)) =>
      f ≫ functorHomEvaluate (weakQuotientCosliceComparisonHom h x) (ULift.up y)) :=
  functorHomEvaluate_point_surjective_of_fiber _ _ y _
    (weakCosliceComparisonFiber_isEssentiallySurjective h x y)

/-- 元の商上の比較二胞体そのものの各成分も、全ての点の射の類を覆う。 -/
theorem weakQuotientMappingComparison_point_surjective (y : C.obj _⦋0⦌) :
    Function.Surjective (fun f : HomotopyCategory.mk pointSpaceVertex ⟶
        HomotopyCategory.mk ((weakSpanKanQuotientDiagram h x).app
          (Opposite.op ⦋0⦌) (ULift.up y)) =>
      f ≫ functorHomEvaluate (weakQuotientMappingComparison h x) (ULift.up y)) := by
  intro z
  let e := (fractionKanQuotientDiagram_classificationIso h x).app (ULift.up y)
  obtain ⟨f, hf⟩ := weakQuotientCosliceComparisonHom_point_surjective h x y (z ≫ e.hom)
  refine ⟨f, (cancel_mono e.hom).mp ?_⟩
  simpa only [_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakQuotientCosliceComparisonHom, functorHomEvaluate_comp,
    e, _root_.SerrePositivity.InfinityCategories.F1.Transport.functorIso_app_hom_evaluate, Category.assoc] using hf

/-- 元の同じ strict Kan 比較成分の coherent 辺も、全ての点の射の類を覆う。 -/
theorem weakSpanKanComparisonValueEdge_point_surjective (c : TransportSimplexCategory B.obj) :
    Function.Surjective (fun f : HomotopyCategory.mk pointSpaceVertex ⟶
        HomotopyCategory.mk (spaceInfinityVertex ((weakSpanKanDiagram i x).obj c)) =>
      f ≫ Truncated.HomotopyCategory.homMk (weakSpanKanComparisonValueEdge h x c).toTruncated) :=
  pointPostcomp_surjective_of_iso_square
    (weakSpanKanQuotientDiagram_initialVertexIso h x c)
    (fractionKanQuotientDiagram_initialVertexIso h x c) _ _
    (weakQuotientMappingComparison_native_component h x c)
    (weakQuotientMappingComparison_point_surjective h x _)

/-- 同じ元の strict Kan 比較の各実成分は、本質的全射。 -/
theorem weakSpanKanMappingComparison_value_isEssentiallySurjective
    (c : TransportSimplexCategory B.obj) :
    IsEssentiallySurjective
      (X := ((weakSpanKanDiagram i x).obj c).obj)
      (Y := ((fractionSimplexKanMappingDiagram q.hom x).obj c).obj)
      ((weakSpanKanMappingComparison h x).app c) :=
  kanMap_isEssentiallySurjective_of_point_surjective _ (weakSpanKanComparisonValueEdge h x c)
    (weakSpanKanComparisonValueEdge_edge h x c)
    (weakSpanKanComparisonValueEdge_point_surjective h x c)

end SerrePositivity.KST.Fibration
