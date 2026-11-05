module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias
public import SerrePositivity.InfinityCategories.F1.KanModels.KanPointComponentComposition
public import SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.WeakIdentityNativeComparison

/-! # 商上の恒等点の比較像を、元の strict Kan 比較による同じ恒等点の実像で表す -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration
end SerrePositivity.KST.Fibration
namespace SerrePositivity.InfinityCategories.Derived.Verdier.Fractions
open SerrePositivity.KST.Fibration
variable {A B C : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.StableCategory.{u}} {i : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap A B} {q : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap B C}
  (h : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.IsVerdierSequence i q) (x : B.obj _⦋0⦌)

/-- 同じ全 strict Kan 比較を、指定した元の恒等点に適用した実像。 -/
def weakIdentityNativeComparisonImage :
    ((_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fractionSimplexKanMappingDiagram q.hom x).obj
      (transportSimplexIndex (n := ⦋0⦌) x)).obj _⦋0⦌ :=
  ((weakSpanKanMappingComparison h x).app
    (transportSimplexIndex (n := ⦋0⦌) x)).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakIdentityKanPoint h x)

/-- 同じ native 比較像を一点空間からの元の射として保持する。 -/
def weakIdentityNativeComparisonImageHom :
    HomotopyCategory.mk pointSpaceVertex ⟶
      HomotopyCategory.mk (spaceInfinityVertex
        ((_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fractionSimplexKanMappingDiagram q.hom x).obj
          (transportSimplexIndex (n := ⦋0⦌) x))) :=
  _root_.SerrePositivity.InfinityCategories.F1.Transport.cosliceFiberPointHom ((pointedSpaceFiberVertexEquiv _).symm
    (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakIdentityNativeComparisonImage h x))

/-- 元の恒等点と同じ native 成分辺との合成は、同じ比較が実際に送る恒等点の像。 -/
theorem weakIdentityNativePointHom_comparison :
    _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakIdentityNativePointHom h x ≫ Truncated.HomotopyCategory.homMk
      (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanComparisonValueEdge h x (transportSimplexIndex (n := ⦋0⦌) x)).toTruncated =
      _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakIdentityNativeComparisonImageHom h x :=
  _root_.SerrePositivity.InfinityCategories.F1.KanModels.kanPointHom_comp_of_edge
    (show (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanDiagram i x).obj (transportSimplexIndex (n := ⦋0⦌) x) ⟶
      (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fractionSimplexKanMappingDiagram q.hom x).obj (transportSimplexIndex (n := ⦋0⦌) x) from
        (weakSpanKanMappingComparison h x).app (transportSimplexIndex (n := ⦋0⦌) x))
    (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanComparisonValueEdge h x (transportSimplexIndex (n := ⦋0⦌) x))
    (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanComparisonValueEdge_edge h x (transportSimplexIndex (n := ⦋0⦌) x))
    (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakIdentityKanPoint h x)

/-- 商上の元の恒等点の像を指定済みの値同型で戻すと、同じ native 比較の実像を回収する。 -/
theorem weakIdentityQuotientPointHom_native_image :
    _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakIdentityQuotientPointHom h x ≫
      functorHomEvaluate (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakQuotientMappingComparison h x)
        (ULift.up (q.hom.app (Opposite.op ⦋0⦌) x)) ≫
      (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fractionIdentityQuotientValueIso h x).hom =
      _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakIdentityNativeComparisonImageHom h x :=
  (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakIdentityQuotientPointHom_native_comparison h x).trans
    (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakIdentityNativePointHom_comparison h x)

/-- 同じ実像を元の coslice fiber へ評価すると、同じ恒等点との指定された同型を回収する。 -/
def weakIdentityNativeComparisonImageUnitIso : VertexIso
    ((_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakIdentityKanTargetEvaluation (q := q) x).app (Opposite.op ⦋0⦌)
      (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakIdentityNativeComparisonImage h x))
    ((F2.continuousKanReplacementUnit.app _).app (Opposite.op ⦋0⦌)
      (edgeToCosliceFiberVertex (SSet.Edge.id (q.hom.app (Opposite.op ⦋0⦌) x)))) :=
  _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakIdentityKanMappingComparisonUnitIso h x

end SerrePositivity.InfinityCategories.Derived.Verdier.Fractions

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakIdentityNativeComparisonImage (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakIdentityNativeComparisonImage := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakIdentityNativeComparisonImage

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakIdentityNativeComparisonImageHom (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakIdentityNativeComparisonImageHom := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakIdentityNativeComparisonImageHom

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakIdentityNativeComparisonImageUnitIso (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakIdentityNativeComparisonImageUnitIso := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakIdentityNativeComparisonImageUnitIso

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakIdentityNativePointHom_comparison := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakIdentityNativePointHom_comparison

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakIdentityQuotientPointHom_native_image := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakIdentityQuotientPointHom_native_image
