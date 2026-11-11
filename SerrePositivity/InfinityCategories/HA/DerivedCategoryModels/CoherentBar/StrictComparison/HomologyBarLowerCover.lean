module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.HomologyBarLowerEmbedding
public import SerrePositivity.DifferentialGraded.Complexes.TensorCoproduct
public import Mathlib.CategoryTheory.Filtered.Basic

/-!
概要：filtered poset 上のホモロジー bar の元は、上界以下の部分から来る。
方針：直和の有限 support に共通上界を取り、同じ係数を持ち上げる。
規約：単体の全ラベルと元の等式を保持する。
使われ方：部分圏での正次数完全性を全体へ運ぶ。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
open CategoryTheory Limits Opposite SSet AlgebraicTopology DifferentialGraded
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] {J : Type u} [PartialOrder J] [IsFiltered J]
  (F : J ⥤ ModuleCat.{u} R)

lemma dgHomologyBarLowerMap_covers (n : ℕ) (z : (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgHomologyBarComplex R F).X n) :
    ∃ (b : J) (a : (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgHomologyBarComplex R (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgHomologyBarLowerDiagram R F b)).X n),
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgHomologyBarLowerMap R F b).f n a = z := by
  classical
  obtain ⟨t, a, ha⟩ := moduleCofan_element_rep R (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgHomologyBarFamily R F (op ⦋n⦌))
    _ (coproductIsCoproduct _) z
  obtain ⟨b, hb⟩ := IsFiltered.sup_objs_exists (t.image (fun s => s.obj (Fin.last n)))
  have hbound (s : (nerve J) _⦋n⦌) (hs : s ∈ t) : s.obj (Fin.last n) ≤ b :=
    leOfHom (hb (Finset.mem_image.mpr ⟨s, hs, rfl⟩)).some
  let w : (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgHomologyBarComplex R (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgHomologyBarLowerDiagram R F b)).X n :=
    ∑ s : t, Sigma.ι (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgHomologyBarFamily R (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgHomologyBarLowerDiagram R F b) (op ⦋n⦌))
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgHomologyBarLiftSimplex s.val b (hbound s.val s.property)) (a s.val)
  refine ⟨b, w, ?_⟩
  dsimp only [w]
  rw [map_sum]
  have hι (s : t) : (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgHomologyBarLowerMap R F b).f n
      (Sigma.ι (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgHomologyBarFamily R (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgHomologyBarLowerDiagram R F b) (op ⦋n⦌))
        (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgHomologyBarLiftSimplex s.val b (hbound s.val s.property)) (a s.val)) =
      Sigma.ι (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgHomologyBarFamily R F (op ⦋n⦌)) s.val (a s.val) :=
    congrArg (fun f => f (a s.val))
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgHomologyBarLowerMap_lift_ι R F s.val b (hbound s.val s.property))
  simp_rw [hι]
  exact (Finset.sum_coe_sort (s := t)
    (f := fun s => Sigma.ι (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgHomologyBarFamily R F (op ⦋n⦌)) s (a s))).trans ha

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
