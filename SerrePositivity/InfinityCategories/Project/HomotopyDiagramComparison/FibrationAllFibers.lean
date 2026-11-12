module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.FibrationTotalComponents

/-!
概要：全空間と底の π_* 同型から任意の底の頂点上の fiber の成分を比較する。
方針：非空 fiber は既存の全次数比較へ渡し、空の fiber の可能性は全空間の成分を移して検査する。
規約：連結成分の全射性を得る際は元の全空間の頂点を明示する。
使われ方：Goerss–Jardine I §§7–8、Sp の引き戻しの Ω 条件の零次数。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped _root_.Simplicial
open SerrePositivity.KST.Spectra SerrePositivity.KST.Spectra.FibrationSquare
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
noncomputable section

/-- 概要：非空な任意の底の頂点上の fiber 射は全空間と底の π_* 同型から π_* 同型となる。
方針：指定 fiber の頂点を参照頂点にし、既存の包含と可換な fiber の比較を適用する。
規約：底の頂点を全空間の頂点の像と同一視する証明を明示して移す。
使われ方：空でない fiber での全基点・全自然数次数の比較。 -/
lemma fibrationFiberMapBase_piIsomorphism_of_vertex {E B E' B' : SSet.{u}}
    [KanComplex E] [KanComplex B] [KanComplex E'] [KanComplex B']
    (p : E ⟶ B) (p' : E' ⟶ B') [Fibration p] [Fibration p']
    (f : E ⟶ E') (g : B ⟶ B') (comm : p ≫ g = f ≫ p')
    (hf : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism f) (hg : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism g)
    (b : B _⦋0⦌) (v : (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanFiber p b) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.fibrationFiberMapBase p p' f g comm b) := by
  let e := (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberι p b).app _ v
  have hb : p.app _ e = b := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiber_vertex_base p b v
  have hb' : p'.app _ (f.app _ e) = g.app _ b :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FibrationSquare.base_eq p p' f g comm e).symm.trans (congrArg (g.app _) hb)
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberMapOver_piIsomorphism p p' f g comm hf hg e b hb (g.app _ b) hb'
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.fibrationFiberMapBase p p' f g comm b) (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.fibrationFiberMapBase_ι p p' f g comm b)

/-- 概要：全空間と底の π_* 同型は任意の底の頂点上で fiber の成分の全射性を導く。
方針：標的 fiber の成分の像を全空間で戻し、底の単射性で源の fiber へ移して参照頂点を得る。
規約：元の全空間の頂点 e₀ を明示し、空の fiber の全基点条件だけには依存しない。
使われ方：全空間の π_* 比較定理に必要な全 fiber の零次数の全射性。 -/
lemma fibrationFiberMapBase_piZero_surjective {E B E' B' : SSet.{u}}
    [KanComplex E] [KanComplex B] [KanComplex E'] [KanComplex B']
    (p : E ⟶ B) (p' : E' ⟶ B') [Fibration p] [Fibration p']
    (f : E ⟶ E') (g : B ⟶ B') (comm : p ≫ g = f ≫ p')
    (hf : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism f) (hg : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism g) (e₀ : E _⦋0⦌) (b : B _⦋0⦌) :
    Function.Surjective (mapπ₀ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.fibrationFiberMapBase p p' f g comm b)) := by
  intro c'
  obtain ⟨v', rfl⟩ := π₀.mk_surjective c'
  obtain ⟨a, ha⟩ := (hf.piZero_bijective_at e₀).surjective
    (π₀.mk ((_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberι p' (g.app _ b)).app _ v'))
  have hp : mapπ₀ p a = π₀.mk b := by
    apply (hg.piZero_bijective_at (p.app _ e₀)).injective
    rw [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.mapPiZero_square p p' f g comm a, ha]
    simp only [mapπ₀_mk, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiber_vertex_base]
  obtain ⟨c, _hc⟩ := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.fibration_componentFiber_exists p b a hp
  obtain ⟨v, _hv⟩ := π₀.mk_surjective c
  have hφ := fibrationFiberMapBase_piIsomorphism_of_vertex p p' f g comm hf hg b v
  exact (hφ.piZero_bijective_at v).surjective (π₀.mk v')

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
