module

public import SerrePositivity.KST.LocalizingInvariants.VerdierInitialConeTensorRefinement
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierQuotientConeRelativeComparison
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.HomotopyPrecompVertex

/-!
概要：回収した二つの左錐の積の全比較を、元の貼合せ境界上で厳密に定値にする。
方針：同じ全錐の slice 比較を境界固定の円柱に実現し、形状同型の逆で制限する。
規約：境界定値性は全円柱の等式であり、点ごとの同型によって代用しない。
使われ方：c5 の次元帰納で、回収済み尾部の比較を元の有限図式と貼り合わせる。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants

namespace VerdierInitialConeTensorRefinement
variable {A₀ B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} {i : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A₀ B} {q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C}
  {h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence i q} {A L : SSet.{u}}
  {p : initialConeTensorCorner A L ⟶ B.obj}
  {H : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[0] : SSet.{u}) A ⊗ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[0] : SSet.{u}) L ⟶ C.obj}
  {hH : initialConeTensorCornerInclusion A L ≫ H = p ≫ q.hom}
  (d : VerdierInitialConeTensorRefinement h A L p H hH)

/-- 同じ実回収の全比較は、貼合せ全境界を全時刻で固定して実現できる。 -/
lemma exists_relativeComparison :
    ∃ J : SSet.Homotopy (d.diagram ≫ q.hom) H,
      (initialConeTensorCornerInclusion A L ▷ (Δ[1] : SSet.{u})) ≫ J.h =
        fst (initialConeTensorCorner A L) Δ[1] ≫ (p ≫ q.hom) ∧
      ∀ x, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge J x).toTruncated := by
  obtain ⟨J, hJ, hi⟩ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.exists_coneRelativeComparison (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCone q.hom d.cone)
    (initialConeTensorQuotientCone q.hom A L p H hH) d.comparison
  let J' : SSet.Homotopy (d.diagram ≫ q.hom) H := {
    h := ((initialConeTensorIso A L).inv ▷ (Δ[1] : SSet.{u})) ≫ J.h
    h₀ := by
      rw [SSet.ι₀_comp_assoc, J.h₀]
      rfl
    h₁ := by
      rw [SSet.ι₁_comp_assoc, J.h₁]
      change (initialConeTensorIso A L).inv ≫ (initialConeTensorIso A L).hom ≫ H = H
      exact Iso.inv_hom_id_assoc _ _
    rel := (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp J (initialConeTensorIso A L).inv).rel }
  refine ⟨J', ?_, ?_⟩
  · change (initialConeTensorCornerInclusion A L ▷ Δ[1]) ≫
      (((initialConeTensorIso A L).inv ▷ Δ[1]) ≫ J.h) = _
    rw [← comp_whiskerRight_assoc, ← initialConeTensorIso_inr]
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
    exact hJ
  · intro x
    have he : (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge J' x).edge =
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge
          (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp J (initialConeTensorIso A L).inv) x).edge := rfl
    apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr he).mpr
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr
      (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.simplicialHomotopyVertexEdge_precomp_edge J (initialConeTensorIso A L).inv x)).mpr
        (hi _)

end VerdierInitialConeTensorRefinement

end SerrePositivity.KST.LocalizingInvariants
