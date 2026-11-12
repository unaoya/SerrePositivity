module

public import SerrePositivity.KST.LocalizingInvariants.InitialConeTensorShape
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierQuotientConeRefinement

/-!
概要：有限図式と尾部を貼った全境界を固定して、二つの左錐の積上へ実図式を回収する。
方針：同じ全形状同型で指定商図式を商錐へ読み、既存の有限全錐回収を実適用する。
規約：全境界は厳密に固定し、元の全商図式への比較は一つの全 slice 同型から作る。
使われ方：c5 の完成側有限境界の正規化における次元延長。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.KST.Fibration
namespace SerrePositivity.KST.LocalizingInvariants

/-- 指定商全図式を、元の有限境界の同じ商錐として読む。 -/
def initialConeTensorQuotientCone {B C : SSet.{u}} (q : B ⟶ C) (A L : SSet.{u})
    (p : initialConeTensorCorner A L ⟶ B)
    (H : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[0] : SSet.{u}) A ⊗ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[0] : SSet.{u}) L ⟶ C)
    (hH : initialConeTensorCornerInclusion A L ≫ H = p ≫ q) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (p ≫ q) :=
  ⟨(initialConeTensorIso A L).hom ≫ H, by
    rw [← Category.assoc, initialConeTensorIso_inr, hH]⟩

/-- 全境界を保つ実錐と、指定商全図式に向かう同じ全 slice 同型。 -/
structure VerdierInitialConeTensorRefinement {A₀ B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}}
    {i : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A₀ B} {q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C} (_h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence i q)
    (A L : SSet.{u}) (p : initialConeTensorCorner A L ⟶ B.obj)
    (H : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[0] : SSet.{u}) A ⊗ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[0] : SSet.{u}) L ⟶ C.obj)
    (hH : initialConeTensorCornerInclusion A L ≫ H = p ≫ q.hom) where
  cone : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p
  comparison : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (X := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (p ≫ q.hom)) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCone q.hom cone)
    (initialConeTensorQuotientCone q.hom A L p H hH)

namespace VerdierInitialConeTensorRefinement
variable {A₀ B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} {i : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A₀ B} {q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C}
  {h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence i q} {A L : SSet.{u}}
  {p : initialConeTensorCorner A L ⟶ B.obj}
  {H : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[0] : SSet.{u}) A ⊗ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[0] : SSet.{u}) L ⟶ C.obj}
  {hH : initialConeTensorCornerInclusion A L ≫ H = p ≫ q.hom}
  (d : VerdierInitialConeTensorRefinement h A L p H hH)

/-- 回収した全実図式。 -/
def diagram : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[0] : SSet.{u}) A ⊗ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[0] : SSet.{u}) L ⟶ B.obj :=
  (initialConeTensorIso A L).inv ≫ d.cone.val

/-- 元の図式と尾部を含む全境界は、元の実図式に厳密に一致する。 -/
lemma boundary : initialConeTensorCornerInclusion A L ≫ d.diagram = p := by
  rw [diagram, ← initialConeTensorIso_inr]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  exact d.cone.property

/-- 同じ一つの全錐同型から、元の全商図式への関手同型を得る。 -/
def iso : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (d.diagram ≫ q.hom) H := by
  have e := (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coneFunctorIsoOfVertexIso _ _ d.comparison).precomp
    (initialConeTensorIso A L).inv
  simpa only [diagram, initialConeTensorQuotientCone, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCone, Category.assoc,
    Iso.inv_hom_id_assoc] using e

/-- 全指定有限境界の各制限も、同じ全実図式の制限として保持される。 -/
lemma restriction {S : SSet.{u}} (f : S ⟶ initialConeTensorCorner A L) :
    (f ≫ initialConeTensorCornerInclusion A L) ≫ d.diagram = f ≫ p := by
  rw [Category.assoc, d.boundary]

end VerdierInitialConeTensorRefinement

/-- 有限な元の全境界と指定商全図式から、全比較付きの実拡張を新仮定なしに回収する。 -/
lemma exists_verdierInitialConeTensorRefinement {A₀ B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}}
    {i : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A₀ B} {q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C} (h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence i q)
    (A L : SSet.{u}) [A.Finite] [L.Finite]
    (p : initialConeTensorCorner A L ⟶ B.obj)
    (H : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[0] : SSet.{u}) A ⊗ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[0] : SSet.{u}) L ⟶ C.obj)
    (hH : initialConeTensorCornerInclusion A L ≫ H = p ≫ q.hom) :
    Nonempty (VerdierInitialConeTensorRefinement h A L p H hH) := by
  obtain ⟨c, ⟨e⟩⟩ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.exists_verdierQuotientConeIsoRefinement h p
    (initialConeTensorQuotientCone q.hom A L p H hH)
  exact ⟨⟨c, e⟩⟩

end SerrePositivity.KST.LocalizingInvariants
