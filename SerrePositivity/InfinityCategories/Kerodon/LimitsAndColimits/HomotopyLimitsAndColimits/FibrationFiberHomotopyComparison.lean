module

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanWhiteheadComparison
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SliceTransport.FibrationAllFibers

/-!
概要：全空間と底の実際の同値が Kan fibration の任意の fiber に誘導する射は同値。
方針：全次数の fiber 比較と π₀ の全射性を分けて確認し、空の対象を含む Whitehead を使う。
規約：源の全空間や fiber の非空性を仮定しない。
使われ方：Goerss–Jardine I §§7–8、Kerodon 7.5.4.6（Tag 03BB）、導来 fiber の標的の同値による比較。

対応節は Kerodon 7.5（Tag 039Y）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open SerrePositivity.KST.Spectra SerrePositivity.KST.Spectra.FibrationSquare
open scoped _root_.Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
noncomputable section

/-- 概要：全空間と底の実際の同値から任意の底の頂点上の fiber の実際の比較射の同値性を得る。
方針：全基点 π_* 同型と独立の π₀ の全射性を検証し、空の fiber も含める。
規約：全空間の参照頂点を追加の前提に置かない。
使われ方：元の q_x の標的の模型を変えたときの導来 fiber の比較。 -/
lemma fibrationFiberMapBase_homotopyEquivalence {E B E' B' : SSet.{u}}
    [KanComplex E] [KanComplex B] [KanComplex E'] [KanComplex B']
    (p : E ⟶ B) (p' : E' ⟶ B') [Fibration p] [Fibration p']
    (f : E ⟶ E') (g : B ⟶ B') (comm : p ≫ g = f ≫ p')
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence f) (hg : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence g)
    (b : B _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.fibrationFiberMapBase p p' f g comm b) := by
  have hfπ := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.kanPiIsomorphism_of_homotopyEquivalence f hf
  have hgπ := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.kanPiIsomorphism_of_homotopyEquivalence g hg
  have hπ : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.fibrationFiberMapBase p p' f g comm b) := by
    intro v n
    exact (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.fibrationFiberMapBase_piIsomorphism_of_vertex p p' f g comm hfπ hgπ b v) v n
  have h₀ : Function.Surjective (mapπ₀ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.fibrationFiberMapBase p p' f g comm b)) := by
    intro c'
    obtain ⟨v', rfl⟩ := π₀.mk_surjective c'
    obtain ⟨a, ha⟩ := hf.mapPiZero_bijective.surjective
      (π₀.mk ((_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberι p' (g.app _ b)).app _ v'))
    have hp : mapπ₀ p a = π₀.mk b := by
      apply hg.mapPiZero_bijective.injective
      rw [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.mapPiZero_square p p' f g comm a, ha]
      simp only [mapπ₀_mk, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiber_vertex_base]
    obtain ⟨c, _hc⟩ := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.fibration_componentFiber_exists p b a hp
    obtain ⟨v, _hv⟩ := π₀.mk_surjective c
    have hv := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.fibrationFiberMapBase_piIsomorphism_of_vertex p p' f g comm hfπ hgπ b v
    exact (hv.piZero_bijective_at v).surjective (π₀.mk v')
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.homotopyEquivalence_of_kanPiIsomorphism_of_piZero_surjective _ hπ h₀

end
end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
