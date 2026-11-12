module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.Diagram
public import SerrePositivity.DifferentialGraded.Complexes.TensorCoproduct
public import SerrePositivity.DifferentialGraded.Module.Disk
public import Mathlib.CategoryTheory.Filtered.Basic

/-!
概要：正規化 graded bar の元は、共通上界を持つ有限個の単体に支えられる。
方針：次数ごとの余積の有限 support 表示と、filtered poset の有限上界を使う。
規約：元の非退化単体ラベルと元そのものの等式を保持する。
使われ方：局所縮約の恒等式を任意の cycle へ適用する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
open CategoryTheory Limits DifferentialGraded SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {J : Type u} [PartialOrder J] (F : J ⥤ ModuleCategory R D)

lemma dgStrictNormalizedDegree_finiteSupport (x : D) (q : ℤ)
    (z : ((moduleDegreeEvaluation R D x q).obj
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedGraded R D (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarStrictDiagram R D F)))) :
    ∃ (t : Finset (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedIndex (nerve J)))
      (a : ∀ s, (moduleDegreeEvaluation R D x q).obj
        (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedFamily R D (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarStrictDiagram R D F) s)),
      ∑ s ∈ t, ((moduleDegreeEvaluation R D x q).map
        (Sigma.ι (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedFamily R D (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarStrictDiagram R D F)) s))
          (a s) = z :=
  moduleCofan_element_rep R
    (fun s => (moduleDegreeEvaluation R D x q).obj
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedFamily R D (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarStrictDiagram R D F) s)) _
    (moduleCoproductDegreeIsColimit R D
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedFamily R D (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarStrictDiagram R D F)) x q) z

lemma dgStrictNormalizedFiniteSupport_bound [IsFiltered J]
    (t : Finset (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedIndex (nerve J))) :
    ∃ b : J, ∀ s ∈ t, s.val.2.obj (Fin.last s.val.1) ≤ b := by
  classical
  let O := t.image (fun s => s.val.2.obj (Fin.last s.val.1))
  obtain ⟨b, hb⟩ := IsFiltered.sup_objs_exists O
  refine ⟨b, ?_⟩
  intro s hs
  exact leOfHom (hb (Finset.mem_image.mpr ⟨s, hs, rfl⟩)).some

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
