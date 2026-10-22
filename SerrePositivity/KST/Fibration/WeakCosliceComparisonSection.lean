module
public import SerrePositivity.KST.Fibration.WeakCosliceScaffoldTriangle
public import SerrePositivity.KST.Fibration.RelativeComparisonRightSection

/-! # 元の K-6 coslice 比較の、同じ商上の実右逆と相対余単位 -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration
variable {A B C : StableCategory.{u}} {i : ExactMap A B} {q : ExactMap B C}
  (h : IsVerdierSequence i q) (x : B.obj _⦋0⦌)

/-- 元の比較は、同じ商の底を厳密に保つ実右逆と全相対写像空間内の余単位を持つ。 -/
theorem exists_weakCosliceComparison_rightSection :
    let pF := smallLeftUnstraighteningProjection (leftStraighteningInfinityDiagram
      (sliceUnderProjection (yonedaEquiv.symm (q.hom.app (Opposite.op ⦋0⦌) x))))
    ∃ (r : smallLeftUnstraightening (leftStraighteningInfinityDiagram
        (sliceUnderProjection (yonedaEquiv.symm (q.hom.app (Opposite.op ⦋0⦌) x)))) ⟶
          smallLeftUnstraightening (weakSpanKanQuotientDiagram h x))
      (hr : r ≫ smallLeftUnstraighteningProjection (weakSpanKanQuotientDiagram h x) =
        smallLeftUnstraighteningProjection (leftStraighteningInfinityDiagram
          (sliceUnderProjection (yonedaEquiv.symm (q.hom.app (Opposite.op ⦋0⦌) x))))),
      Nonempty (VertexIso
        (relativeFunctorVertex pF pF (r ≫ weakQuotientCosliceComparison h x)
          (by rw [Category.assoc, weakQuotientCosliceComparison_projection, hr]))
        (relativeFunctorVertex pF pF (𝟙 _) (Category.id_comp _))) :=
  exists_relativeRightSection_of_compositeIso _ _ _
    (weakQuotientCosliceUnit h x) (weakQuotientCosliceComparison h x)
    (scaffoldPointedReconstruction
      (sliceUnderProjection (yonedaEquiv.symm (q.hom.app (Opposite.op ⦋0⦌) x))))
    (weakQuotientCosliceUnit_projection h x) (weakQuotientCosliceComparison_projection h x)
    (scaffoldPointedReconstruction_projection _)
    (scaffoldPointedReconstruction_isPrecompositionEquivalence _)
    (weakCosliceComposite_scaffold_relativeIso h x)

/-- 同じ相対三角形から得る、元の実 coslice 比較の右逆。 -/
def weakCosliceComparisonRightSection := (exists_weakCosliceComparison_rightSection h x).choose

/-- 選んだ同じ実右逆は、元の Verdier 商への射影を厳密に保つ。 -/
theorem weakCosliceComparisonRightSection_projection :
    weakCosliceComparisonRightSection h x ≫
      smallLeftUnstraighteningProjection (weakSpanKanQuotientDiagram h x) =
    smallLeftUnstraighteningProjection (leftStraighteningInfinityDiagram
      (sliceUnderProjection (yonedaEquiv.symm (q.hom.app (Opposite.op ⦋0⦌) x)))) :=
  (exists_weakCosliceComparison_rightSection h x).choose_spec.choose

/-- 右逆と元の比較の合成は、同じ底上の全相対写像空間内で恒等写像と同型。 -/
def weakCosliceComparisonRightSection_relativeCounit :
    let pF := smallLeftUnstraighteningProjection (leftStraighteningInfinityDiagram
      (sliceUnderProjection (yonedaEquiv.symm (q.hom.app (Opposite.op ⦋0⦌) x))))
    VertexIso
      (relativeFunctorVertex pF pF
        (weakCosliceComparisonRightSection h x ≫ weakQuotientCosliceComparison h x)
        (by rw [Category.assoc, weakQuotientCosliceComparison_projection,
          weakCosliceComparisonRightSection_projection]))
      (relativeFunctorVertex pF pF (𝟙 _) (Category.id_comp _)) :=
  (exists_weakCosliceComparison_rightSection h x).choose_spec.choose_spec.some

end SerrePositivity.KST.Fibration
