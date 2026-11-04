module
public import SerrePositivity.InfinityCategories.F1.KanModels.KanPointComponentComposition
public import SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.WeakIdentityNativeComparison

/-! # 商上の恒等点の比較像を、元の strict Kan 比較による同じ恒等点の実像で表す -/

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

/-- 同じ全 strict Kan 比較を、指定した元の恒等点に適用した実像。 -/
def weakIdentityNativeComparisonImage :
    ((fractionSimplexKanMappingDiagram q.hom x).obj
      (transportSimplexIndex (n := ⦋0⦌) x)).obj _⦋0⦌ :=
  ((weakSpanKanMappingComparison h x).app
    (transportSimplexIndex (n := ⦋0⦌) x)).app (Opposite.op ⦋0⦌) (weakIdentityKanPoint h x)

/-- 同じ native 比較像を一点空間からの元の射として保持する。 -/
def weakIdentityNativeComparisonImageHom :
    HomotopyCategory.mk pointSpaceVertex ⟶
      HomotopyCategory.mk (spaceInfinityVertex
        ((fractionSimplexKanMappingDiagram q.hom x).obj
          (transportSimplexIndex (n := ⦋0⦌) x))) :=
  cosliceFiberPointHom ((pointedSpaceFiberVertexEquiv _).symm
    (weakIdentityNativeComparisonImage h x))

/-- 元の恒等点と同じ native 成分辺との合成は、同じ比較が実際に送る恒等点の像。 -/
theorem weakIdentityNativePointHom_comparison :
    weakIdentityNativePointHom h x ≫ Truncated.HomotopyCategory.homMk
      (weakSpanKanComparisonValueEdge h x (transportSimplexIndex (n := ⦋0⦌) x)).toTruncated =
      weakIdentityNativeComparisonImageHom h x :=
  kanPointHom_comp_of_edge
    (show (weakSpanKanDiagram i x).obj (transportSimplexIndex (n := ⦋0⦌) x) ⟶
      (fractionSimplexKanMappingDiagram q.hom x).obj (transportSimplexIndex (n := ⦋0⦌) x) from
        (weakSpanKanMappingComparison h x).app (transportSimplexIndex (n := ⦋0⦌) x))
    (weakSpanKanComparisonValueEdge h x (transportSimplexIndex (n := ⦋0⦌) x))
    (weakSpanKanComparisonValueEdge_edge h x (transportSimplexIndex (n := ⦋0⦌) x))
    (weakIdentityKanPoint h x)

/-- 商上の元の恒等点の像を指定済みの値同型で戻すと、同じ native 比較の実像を回収する。 -/
theorem weakIdentityQuotientPointHom_native_image :
    weakIdentityQuotientPointHom h x ≫
      functorHomEvaluate (weakQuotientMappingComparison h x)
        (ULift.up (q.hom.app (Opposite.op ⦋0⦌) x)) ≫
      (fractionIdentityQuotientValueIso h x).hom =
      weakIdentityNativeComparisonImageHom h x :=
  (weakIdentityQuotientPointHom_native_comparison h x).trans
    (weakIdentityNativePointHom_comparison h x)

/-- 同じ実像を元の coslice fiber へ評価すると、同じ恒等点との指定された同型を回収する。 -/
def weakIdentityNativeComparisonImageUnitIso : VertexIso
    ((weakIdentityKanTargetEvaluation (q := q) x).app (Opposite.op ⦋0⦌)
      (weakIdentityNativeComparisonImage h x))
    ((F2.continuousKanReplacementUnit.app _).app (Opposite.op ⦋0⦌)
      (edgeToCosliceFiberVertex (SSet.Edge.id (q.hom.app (Opposite.op ⦋0⦌) x)))) :=
  weakIdentityKanMappingComparisonUnitIso h x

end SerrePositivity.KST.Fibration
