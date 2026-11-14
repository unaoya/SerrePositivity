module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.NativeDegeneracy
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.CoherentBar.Faces.DGCoherentBarCuts
/-!
概要：最初の退化辺の coherent 係数は同じ頂点の単位である。
方針：dg nerve の collapsed-pair 公式と、最初の prefix の厳密なラベル等式を使う。
規約：単位の比較は端点輸送付き異種等号で保持する。
使われ方：退化位置零における面項と長さ一 prefix 項の相殺。
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

lemma dgCoherentBar_native_degenerateEdge_unit (s : I _⦋0⦌) :
    HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentDiagramTopRaw F (I.σ 0 s)) (_root_.SerrePositivity.DifferentialGraded.unitElement R (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentDiagramVertex F s)).val := by
  have h : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentDiagramSimplex F (I.σ 0 s) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R C).σ 0 (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentDiagramSimplex F s) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentDiagramSimplex_map F (0 : Fin 1).predAboveOrderHom s
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentDiagramTopRaw
  rw [h]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.σ_hom_of_collapsed_pair R C 0 (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentDiagramSimplex F s)
    Finset.univ 0 (Fin.last 1) 0 (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentDiagramTop_card 0)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentDiagramTop_min 0) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentDiagramTop_max 0) (by simp)
    (Finset.mem_univ _) (Finset.mem_univ _) (by simp)

lemma dgCoherentBar_native_degenerateEdge_unit_transported (s : I _⦋0⦌) :
    HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentDiagramTop F (I.σ 0 s)) (_root_.SerrePositivity.DifferentialGraded.unitElement R (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentDiagramVertex F s)).val := by
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentDiagramTop
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHomTransport_heq _ _ _ _).trans
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBar_native_degenerateEdge_unit F s)

lemma dgCoherentBarPrefix_degeneracy_zero {n : ℕ} (s : I _⦋n⦌) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarPrefix (I.σ 0 s) 1 (by omega)).2 =
      I.σ 0 (I.map (SimplexCategory.const ⦋0⦌ ⦋n⦌ 0).op s) := by
  have horder : SimplexCategory.mkHom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarPrefixOrder (n + 1) 1 (by omega)) ≫
      SimplexCategory.σ (0 : Fin (n + 1)) =
      SimplexCategory.σ (0 : Fin 1) ≫ SimplexCategory.const ⦋0⦌ ⦋n⦌ 0 := by
    ext a
    fin_cases a <;> rfl
  have h := congrArg (fun f => I.map f.op s) horder
  simpa only [op_comp, CategoryTheory.Functor.map_comp, types_comp_apply,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarPrefix, SimplicialObject.σ] using h

lemma dgCoherentBarTail_degeneracy_zero {n : ℕ} (s : I _⦋n⦌) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarTail (I.σ 0 s) 1 (by omega) = ⟨n, s⟩ := by
  have horder : SimplexCategory.mkHom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarTailOrder (n + 1) 1 (by omega)) ≫
      SimplexCategory.σ (0 : Fin (n + 1)) = 𝟙 ⦋n⦌ := by
    ext a
    change ((0 : Fin (n + 1)).predAbove
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarTailOrder (n + 1) 1 (by omega) a)).val = a.val
    have ha : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarTailOrder (n + 1) 1 (by omega) a = a.succ :=
      Fin.ext (by dsimp [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarTailOrder]; omega)
    rw [ha, Fin.predAbove_zero_succ]
  have h := congrArg (fun f => I.map f.op s) horder
  simp only [op_comp, CategoryTheory.Functor.map_comp, types_comp_apply] at h
  unfold _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarTail
  simpa [SimplicialObject.σ] using congrArg
    (fun t => (⟨n, t⟩ : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarIndex I)) h

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar
