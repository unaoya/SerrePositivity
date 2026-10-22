module

public import SerrePositivity.InfinityCategories.F2.Compact.RepresentableCoslice
public import SerrePositivity.InfinityCategories.F2.Compact.Preservation
public import SerrePositivity.InfinityCategories.F1.LeftStraighteningInfinityReconstruction

/-!
概要：元の共変 Hom 関手を、同じ coslice の実際の全空間表現へ全自然同型で比較する。
方針：保存済みの coslice 分類比較と元の native 表現との全比較を合成する。
規約：元の Hom・coslice・表現を固定。使われ方：compact 性による元の指定余錐像の余極限性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Compact

/-- 元の同じ対象からの coslice の native な全空間表現。 -/
def nativeCosliceRepresentation {C : SSet.{u}} [Quasicategory C] (x : C _⦋0⦌) :=
  nativeLeftTransportRepresentation (sliceUnderProjection (SSet.yonedaEquiv.symm x))

/-- 元の共変 Hom と、同じ coslice の同じ表現図式との全自然比較。 -/
def nativeCovariantRepresentationIso {C : SSet.{u}} [Quasicategory C] (x : C _⦋0⦌) :
    FunctorIso (covariantRepresentableInfinity x) (nativeCosliceRepresentation x).diagram :=
  covariantRepresentableInfinity_cosliceIso x ≪≫
    leftStraighteningInfinityDiagram_representationIso _ (nativeCosliceRepresentation x)

/-- 元の対象の compact 性は、同じ coslice の実表現図式による余極限保存を与える。 -/
lemma IsKappaCompact.nativeCoslice_preserves {κ : Cardinal.{u}}
    {C : SSet.{max u v}} [Quasicategory C] {x : C _⦋0⦌}
    (h : IsKappaCompact.{u, v} κ x) :
    PreservesKappaFilteredColimits.{u, v} κ (nativeCosliceRepresentation x).diagram :=
  h.of_functorIso (nativeCovariantRepresentationIso x)

end SerrePositivity.InfinityCategories.F2.Compact
