module

public import SerrePositivity.KST.LocalizingInvariants.VerdierInitialConeTensorRefinement
public import SerrePositivity.KST.LocalizingInvariants.SpecifiedBoundaryIsoNormalization

/-!
概要：指定商境界の全比較辺を保持して、元の有限図式と尾部の実拡張を回収する。
方針：指定境界辺を持ち上げて厳密化し、その同じ全商図式へ有限全錐回収を実適用する。
規約：境界一致を未供給仮定に置き換えず、元の全境界比較一次単体を保持する。
使われ方：c5 の有限境界付き全族を同じ実図式へ正規化するための次元延長。
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

/-- 指定境界比較を保持した厳密化と、それを実消費した有限全図式の回収。 -/
structure VerdierInitialConeTensorBoundary {A₀ B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}}
    {i : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A₀ B} {q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C} (h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence i q)
    (A L : SSet.{u}) (p : initialConeTensorCorner A L ⟶ B.obj)
    (H : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[0] : SSet.{u}) A ⊗ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[0] : SSet.{u}) L ⟶ C.obj)
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (initialConeTensorCornerInclusion A L ≫ H) (p ≫ q.hom)) where
  normalization : SpecifiedBoundaryIsoNormalization (initialConeTensorCornerInclusion A L)
    H (p ≫ q.hom) e
  refinement : VerdierInitialConeTensorRefinement h A L p normalization.diagram
    normalization.boundary

namespace VerdierInitialConeTensorBoundary
variable {A₀ B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} {i : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A₀ B} {q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C}
  {h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence i q} {A L : SSet.{u}}
  {p : initialConeTensorCorner A L ⟶ B.obj}
  {H : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[0] : SSet.{u}) A ⊗ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[0] : SSet.{u}) L ⟶ C.obj}
  {e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (initialConeTensorCornerInclusion A L ≫ H) (p ≫ q.hom)}
  (d : VerdierInitialConeTensorBoundary h A L p H e)

/-- 元の全実境界を持つ、回収済みの同じ実全図式。 -/
def diagram : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[0] : SSet.{u}) A ⊗ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[0] : SSet.{u}) L ⟶ B.obj :=
  d.refinement.diagram

lemma boundary : initialConeTensorCornerInclusion A L ≫ d.diagram = p :=
  d.refinement.boundary

/-- 指定された元の全商図式への、一つの回収を通じた全比較。 -/
def iso : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (d.diagram ≫ q.hom) H :=
  d.refinement.iso ≪≫ d.normalization.iso.symm

/-- 指定されたパラメータ辺の商後可逆性は、同じ全比較によって保たれる。 -/
lemma invertsEdges (W : Set
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[0] : SSet.{u}) A ⊗ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[0] : SSet.{u}) L) _⦋1⦌))
    (hW : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InvertsEdges H W) : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InvertsEdges (d.diagram ≫ q.hom) W :=
  (invertsEdges_functorIso_iff d.iso W).mpr hW

end VerdierInitialConeTensorBoundary

/-- 有限全境界の指定同型から、同じ境界辺を保持する実全図式を回収する。 -/
lemma exists_verdierInitialConeTensorBoundary {A₀ B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}}
    {i : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A₀ B} {q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C} (h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence i q)
    (A L : SSet.{u}) [A.Finite] [L.Finite]
    (p : initialConeTensorCorner A L ⟶ B.obj)
    (H : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[0] : SSet.{u}) A ⊗ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[0] : SSet.{u}) L ⟶ C.obj)
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (initialConeTensorCornerInclusion A L ≫ H) (p ≫ q.hom)) :
    Nonempty (VerdierInitialConeTensorBoundary h A L p H e) := by
  obtain ⟨n⟩ := exists_specifiedBoundaryIsoNormalization
    (initialConeTensorCornerInclusion A L) H (p ≫ q.hom) e
  obtain ⟨d⟩ := exists_verdierInitialConeTensorRefinement h A L p n.diagram n.boundary
  exact ⟨⟨n, d⟩⟩

end SerrePositivity.KST.LocalizingInvariants
