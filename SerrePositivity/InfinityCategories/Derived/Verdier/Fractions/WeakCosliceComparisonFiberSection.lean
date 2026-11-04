module
public import SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.WeakCosliceComparisonSection
public import SerrePositivity.InfinityCategories.F1.Transport.FunctorIsoValue
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.RelativeFunctorFiberHom

/-! # 同じ商上の実右逆と余単位を、全ての元の fiber に制限する -/

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
  (h : IsVerdierSequence i q) (x : B.obj _⦋0⦌) (y : C.obj _⦋0⦌)

/-- 元の同じ商上の coslice 比較の、指定した実 fiber での作用。 -/
def weakCosliceComparisonFiber :=
  vertexFiberMap (smallLeftUnstraighteningProjection (weakSpanKanQuotientDiagram h x))
    (smallLeftUnstraighteningProjection (leftStraighteningInfinityDiagram
      (sliceUnderProjection (yonedaEquiv.symm (q.hom.app (Opposite.op ⦋0⦌) x)))))
    (weakQuotientCosliceComparison h x) (weakQuotientCosliceComparison_projection h x) y

/-- 同じ商上の一つの右逆を、指定した元の fiber に制限した実右逆。 -/
def weakCosliceComparisonFiberRightSection :=
  vertexFiberMap
    (smallLeftUnstraighteningProjection (leftStraighteningInfinityDiagram
      (sliceUnderProjection (yonedaEquiv.symm (q.hom.app (Opposite.op ⦋0⦌) x)))))
    (smallLeftUnstraighteningProjection (weakSpanKanQuotientDiagram h x))
    (weakCosliceComparisonRightSection h x) (weakCosliceComparisonRightSection_projection h x) y

/-- 相対余単位は、全ての元の実 fiber の同じ二つの写像間の関手同型へ制限される。 -/
def weakCosliceComparisonFiberRightSection_counit :
    FunctorIso (weakCosliceComparisonFiberRightSection h x y ≫ weakCosliceComparisonFiber h x y)
      (𝟙 _) := by
  let p := smallLeftUnstraighteningProjection (weakSpanKanQuotientDiagram h x)
  let r := smallLeftUnstraighteningProjection (leftStraighteningInfinityDiagram
    (sliceUnderProjection (yonedaEquiv.symm (q.hom.app (Opposite.op ⦋0⦌) x))))
  let f := weakCosliceComparisonRightSection h x
  let g := weakQuotientCosliceComparison h x
  have hf : f ≫ p = r := weakCosliceComparisonRightSection_projection h x
  have hg : g ≫ r = p := weakQuotientCosliceComparison_projection h x
  have he := VertexIso.map (weakCosliceComparisonRightSection_relativeCounit h x)
    (relativeFunctorFiberHom r r y)
  rw [relativeFunctorFiberHom_vertex r r y (f ≫ g) (by rw [Category.assoc, hg, hf]),
    relativeFunctorFiberHom_vertex r r y (𝟙 _) (Category.id_comp r)] at he
  change FunctorIso (vertexFiberMap r p f hf y ≫ vertexFiberMap p r g hg y) (𝟙 _)
  rw [vertexFiberMap_comp]
  simpa only [vertexFiberMap_id] using he

/-- 元の比較は全ての元の実 fiber で本質的全射。充満忠実性はここからは結論しない。 -/
theorem weakCosliceComparisonFiber_isEssentiallySurjective :
    IsEssentiallySurjective (weakCosliceComparisonFiber h x y) := by
  intro z
  refine ⟨(weakCosliceComparisonFiberRightSection h x y).app (Opposite.op ⦋0⦌) z, ⟨?_⟩⟩
  exact functorIsoValue (weakCosliceComparisonFiberRightSection_counit h x y) z

end SerrePositivity.KST.Fibration
