module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.NativeDegeneracy
public import SerrePositivity.InfinityCategories.Derived.DGCoherentBarCuts
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
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
open scoped Simplicial
variable {R : Type u} [CommRing R] {C : Type v} [DGCategory R C]
  {I : SSet.{u}} (F : (SSet.uliftFunctor.{v, u}).obj I ⟶ dgNerve R C)

lemma dgCoherentBar_native_degenerateEdge_unit (s : I _⦋0⦌) :
    HEq (coherentDiagramTopRaw F (I.σ 0 s)) (unitElement R (coherentDiagramVertex F s)).val := by
  have h : coherentDiagramSimplex F (I.σ 0 s) =
      (dgNerve R C).σ 0 (coherentDiagramSimplex F s) :=
    coherentDiagramSimplex_map F (0 : Fin 1).predAboveOrderHom s
  unfold coherentDiagramTopRaw
  rw [h]
  exact dgNerve.σ_hom_of_collapsed_pair R C 0 (coherentDiagramSimplex F s)
    Finset.univ 0 (Fin.last 1) 0 (coherentDiagramTop_card 0)
    (coherentDiagramTop_min 0) (coherentDiagramTop_max 0) (by simp)
    (Finset.mem_univ _) (Finset.mem_univ _) (by simp)

lemma dgCoherentBar_native_degenerateEdge_unit_transported (s : I _⦋0⦌) :
    HEq (coherentDiagramTop F (I.σ 0 s)) (unitElement R (coherentDiagramVertex F s)).val := by
  unfold coherentDiagramTop
  exact (gradedHomTransport_heq _ _ _ _).trans
    (dgCoherentBar_native_degenerateEdge_unit F s)

lemma dgCoherentBarPrefix_degeneracy_zero {n : ℕ} (s : I _⦋n⦌) :
    (dgCoherentBarPrefix (I.σ 0 s) 1 (by omega)).2 =
      I.σ 0 (I.map (SimplexCategory.const ⦋0⦌ ⦋n⦌ 0).op s) := by
  have horder : SimplexCategory.mkHom (dgCoherentBarPrefixOrder (n + 1) 1 (by omega)) ≫
      SimplexCategory.σ (0 : Fin (n + 1)) =
      SimplexCategory.σ (0 : Fin 1) ≫ SimplexCategory.const ⦋0⦌ ⦋n⦌ 0 := by
    ext a
    fin_cases a <;> rfl
  have h := congrArg (fun f => I.map f.op s) horder
  simpa only [op_comp, CategoryTheory.Functor.map_comp, types_comp_apply,
    dgCoherentBarPrefix, SimplicialObject.σ] using h

lemma dgCoherentBarTail_degeneracy_zero {n : ℕ} (s : I _⦋n⦌) :
    dgCoherentBarTail (I.σ 0 s) 1 (by omega) = ⟨n, s⟩ := by
  have horder : SimplexCategory.mkHom (dgCoherentBarTailOrder (n + 1) 1 (by omega)) ≫
      SimplexCategory.σ (0 : Fin (n + 1)) = 𝟙 ⦋n⦌ := by
    ext a
    change ((0 : Fin (n + 1)).predAbove
      (dgCoherentBarTailOrder (n + 1) 1 (by omega) a)).val = a.val
    have ha : dgCoherentBarTailOrder (n + 1) 1 (by omega) a = a.succ :=
      Fin.ext (by dsimp [dgCoherentBarTailOrder]; omega)
    rw [ha, Fin.predAbove_zero_succ]
  have h := congrArg (fun f => I.map f.op s) horder
  simp only [op_comp, CategoryTheory.Functor.map_comp, types_comp_apply] at h
  unfold dgCoherentBarTail
  simpa [SimplicialObject.σ] using congrArg
    (fun t => (⟨n, t⟩ : dgCoherentBarIndex I)) h

end SerrePositivity.InfinityCategories
