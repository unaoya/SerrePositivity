module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.CoherentBar.Structure.DGCoherentBarGraded
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.CoherentDiagramVertexMap

/-!
概要：元の単体の任意の非空部分集合を同じ bar の単体ラベルとして実現する。
方針：有限順序による列挙で元の図式を制限し、最小点の対象を厳密に比較する。
規約：元の全単体を保ち、退化単体も除かない。
使われ方：Bianchi 恒等式に与える、最後の頂点への bar 包含係数。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
open scoped _root_.Simplicial
variable {I : SSet.{u}}

def dgCoherentBarSubsetLabel {n : ℕ} (σ : I _⦋n⦌)
    (J : Finset (Fin (n + 1))) (r : ℕ) (hc : J.card = r + 1) : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarIndex I :=
  ⟨r, I.map (SimplexCategory.mkHom (J.orderEmbOfFin hc).toOrderHom).op σ⟩

lemma dgCoherentBarSubsetLabel_univ {n : ℕ} (σ : I _⦋n⦌) :
    dgCoherentBarSubsetLabel σ Finset.univ n (by simp) = ⟨n, σ⟩ := by
  have hefun : (fun i : Fin (n + 1) => i) =
      (Finset.univ : Finset (Fin (n + 1))).orderEmbOfFin (by simp) :=
    Finset.orderEmbOfFin_unique (by simp) (fun _ => Finset.mem_univ _) strictMono_id
  have he : SimplexCategory.mkHom
      ((Finset.univ : Finset (Fin (n + 1))).orderEmbOfFin (by simp)).toOrderHom =
      𝟙 ⦋n⦌ := by
    ext i : 3
    exact congrFun hefun.symm i
  unfold dgCoherentBarSubsetLabel
  rw [he]
  change (⟨n, I.map (𝟙 _).op σ⟩ : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarIndex I) = ⟨n, σ⟩
  simp only [op_id, CategoryTheory.Functor.map_id, types_id_apply]

variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]
  (F : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (RightModule R D))

lemma dgCoherentBarSubsetLabel_source {n : ℕ} (σ : I _⦋n⦌)
    (J : Finset (Fin (n + 1))) (r : ℕ) (hc : J.card = r + 1)
    (hJ : J.Nonempty) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSource R D F (dgCoherentBarSubsetLabel σ J r hc) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentDiagramSimplex F σ).obj (J.min' hJ) := by
  have he : J.orderEmbOfFin hc (0 : Fin (r + 1)) = J.min' hJ :=
    Finset.orderEmbOfFin_zero hc (Nat.succ_pos r)
  have hv := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentDiagramVertex_map F
    (SimplexCategory.mkHom (J.orderEmbOfFin hc).toOrderHom) σ (0 : Fin (r + 1))
  change _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSource R D F (dgCoherentBarSubsetLabel σ J r hc) = _ at hv
  change _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSource R D F (dgCoherentBarSubsetLabel σ J r hc) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentDiagramVertex F (I.map (SimplexCategory.const ⦋0⦌ ⦋n⦌
      ((J.orderEmbOfFin hc) 0)).op σ) at hv
  rw [he] at hv
  exact hv.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentDiagramSimplex_obj F σ (J.min' hJ)).symm

end SerrePositivity.InfinityCategories.Project.DerivedCategories
