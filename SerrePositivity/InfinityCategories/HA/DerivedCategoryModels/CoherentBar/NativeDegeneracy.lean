module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.CoherentDiagramTopHom
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Computations
public import Mathlib.AlgebraicTopology.SimplicialSet.Degenerate
/-!
概要：native dg nerve 値図式の退化三角形では最上 cochain は必ず零になる。
方針：図式の単体的自然性と dg nerve の退化成分公式を使う。
規約：全単体を独立因子に持つ未正規化 bar の包含を余錐成分と即断しない。
使われ方：bar の native 余錐に必要な退化整合性の検査。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar
open CategoryTheory DifferentialGraded SSet
open scoped _root_.Simplicial
variable {R : Type u} [CommRing R] {C : Type v} [_root_.SerrePositivity.DifferentialGraded.DGCategory R C]
  {I : SSet.{u}} (F : (SSet.uliftFunctor.{v, u}).obj I ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R C)

lemma dgCoherentBar_native_degenerateTriangle (s : I _⦋1⦌) (i : Fin 2) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentDiagramTopRaw F (I.σ i s) = 0 := by
  have h : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentDiagramSimplex F (I.σ i s) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R C).σ i (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentDiagramSimplex F s) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentDiagramSimplex_map F i.predAboveOrderHom s
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentDiagramTopRaw
  rw [h]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.σ_hom_eq_zero R C i (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentDiagramSimplex F s)
    Finset.univ 0 (Fin.last 2) (-1) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentDiagramTop_card 1)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentDiagramTop_min 1) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentDiagramTop_max 1) (by simp)
    (Finset.mem_univ _) (Finset.mem_univ _) (by simp)

lemma dgCoherentBar_native_degenerateTop {n : ℕ} (s : I _⦋n + 1⦌)
    (i : Fin (n + 2)) : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentDiagramTopRaw F (I.σ i s) = 0 := by
  have h : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentDiagramSimplex F (I.σ i s) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R C).σ i (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentDiagramSimplex F s) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentDiagramSimplex_map F i.predAboveOrderHom s
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentDiagramTopRaw
  rw [h]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.σ_hom_eq_zero R C i (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentDiagramSimplex F s)
    Finset.univ 0 (Fin.last (n + 2)) (-((n + 1 : ℕ) : ℤ))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentDiagramTop_card (n + 1)) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentDiagramTop_min (n + 1))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentDiagramTop_max (n + 1)) (by simp)
    (Finset.mem_univ _) (Finset.mem_univ _) (by simp)

lemma dgCoherentBar_native_degenerateTop_transported {n : ℕ} (s : I _⦋n + 1⦌)
    (i : Fin (n + 2)) : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentDiagramTop F (I.σ i s) = 0 := by
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentDiagramTop
  rw [dgCoherentBar_native_degenerateTop]
  exact map_zero _

lemma dgCoherentBar_native_top_eq_zero_of_degenerate {n : ℕ} (s : I _⦋n + 2⦌)
    (hs : s ∈ I.degenerate (n + 2)) : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentDiagramTopRaw F s = 0 := by
  rw [I.degenerate_eq_iUnion_range_σ] at hs
  obtain ⟨i, t, rfl⟩ := Set.mem_iUnion.mp hs
  exact dgCoherentBar_native_degenerateTop F t i

lemma dgCoherentBar_native_top_transported_eq_zero_of_degenerate {n : ℕ}
    (s : I _⦋n + 2⦌) (hs : s ∈ I.degenerate (n + 2)) : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentDiagramTop F s = 0 := by
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentDiagramTop
  rw [_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBar_native_top_eq_zero_of_degenerate F s hs]
  exact map_zero _

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar
