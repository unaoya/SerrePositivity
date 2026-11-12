module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias

public import SerrePositivity.KST.LocalizingInvariants.SpanEndpointShape
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.FixedFractionTriangles
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.InnerFibrations.InnerFiber
public import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.Inner.PushoutProduct

/-!
概要：両端固定の分母付き span と実三角補完は quasicategory をなす。
方針：境界を horn の実部分形状へ同定し、制限の inner fibration 性を全部分圏へ移す。
規約：分母集合は任意。終域の局所化や写像空間比較の同値性は仮定しない。
使われ方：分数 span の ∞ 圏とその亜群化を扱うための元の圏構造。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants
end SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions
open _root_.SerrePositivity.KST.LocalizingInvariants

instance markedSpans_quasicategory (X : SSet.{u}) [Quasicategory X]
    (W : Set (X _⦋1⦌)) : Quasicategory (markedSpans X W) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.InnerFibrations.fullSubcomplexOnVertices_quasicategory _ _

instance markedSpanBoundary_innerFibration (X : SSet.{u}) [Quasicategory X]
    (W : Set (X _⦋1⦌)) : InnerFibration (markedSpanBoundary X W) := by
  rw [markedSpanBoundary_restriction]
  have : InnerFibration (markedSpanInclusion X W) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.InnerFibrations.fullSubcomplexOnVertices_innerFibration _ _
  exact ⟨innerFibrations.comp_mem _ _ (mem_innerFibrations _) (mem_innerFibrations _)⟩

instance fixedMarkedSpans_quasicategory (X : SSet.{u}) [Quasicategory X]
    (W : Set (X _⦋1⦌)) (x y : X _⦋0⦌) : Quasicategory (fixedMarkedSpans X W x y) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.InnerFibrations.innerFibration_vertexFiber_quasicategory _ _

instance fixedFractionTriangles_quasicategory {X Q : SSet.{u}}
    [Quasicategory X] [Quasicategory Q] (F : X ⟶ Q) (W : Set (X _⦋1⦌))
    (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InvertsEdges F W) (x y : X _⦋0⦌) : Quasicategory (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.fixedFractionTriangles F W hF x y) :=
  quasicategory_of_innerFibration (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.fixedFractionTriangleProjection F W hF x y)

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.fixedFractionTriangles_quasicategory (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.fixedFractionTriangles_quasicategory := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.fixedFractionTriangles_quasicategory

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.fixedMarkedSpans_quasicategory (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.fixedMarkedSpans_quasicategory := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.fixedMarkedSpans_quasicategory

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.markedSpanBoundary_innerFibration (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.markedSpanBoundary_innerFibration := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.markedSpanBoundary_innerFibration

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.markedSpans_quasicategory (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.markedSpans_quasicategory := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.markedSpans_quasicategory
