module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.AnodyneIntervalEndpoints
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FiberComponents
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FibrationBoundary
public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.Subdivision.HomotopyComponents
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.HomotopyDegreeZero
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.HomotopyGroups
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.HomotopyIndexing
public import SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FromTopologicalSpacesToSimplicialSets.HomotopyZeroRelations

/-!
概要：Kan fibration の連結成分を任意の底の頂点上の fiber に移す。
方針：底の連結成分の等号を一本の辺に直し、指定した始点から持ち上げる。
規約：fiber に先に参照頂点があることを仮定しない。
使われ方：Goerss–Jardine I §§7–8、Sp の引き戻しの零次数の比較と空の fiber の検査。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open SerrePositivity.SimplicialModel SerrePositivity.KST.Spectra
open scoped _root_.Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
noncomputable section

/-- 概要：全空間の頂点の像と同じ底の成分にある頂点は同じ全空間成分から持ち上がる。
方針：零次数の類の等号から辺を取り、Kan fibration の端点持ち上げを使う。
規約：指定した fiber の非空性を前提にせず、結論として持ち上げる頂点を得る。
使われ方：任意の底の頂点上の fiber での連結成分の完全性。 -/
lemma fibration_vertex_in_component {E B : SSet.{u}} [KanComplex E] [KanComplex B]
    (p : E ⟶ B) [Fibration p] (e : E _⦋0⦌) (b : B _⦋0⦌)
    (hb : π₀.mk (p.app _ e) = π₀.mk b) :
    ∃ e' : E _⦋0⦌, p.app _ e' = b ∧ π₀.mk e' = π₀.mk e := by
  let s : E.PtSimplex 0 e := (PtSimplex.equiv₀ e).symm e
  let t : B.PtSimplex 0 (p.app _ e) := (PtSimplex.equiv₀ _).symm b
  have heq : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.mk 0 t = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.mk 0 (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.mapSimplex p rfl s) := by
    change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyZero.mk t = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyZero.map p rfl (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.point 0)
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyZero.equivPiZero.injective
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyZero.equivPiZero_mk, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyZero.equivPiZero_map,
      _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanHomotopyZero.equivPiZero_point, Equiv.apply_symm_apply, mapπ₀_mk]
    exact hb.symm
  obtain ⟨r⟩ := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FromTopologicalSpacesToSimplicialSets.KanHomotopy.mk_eq_iff_relStruct 0 t (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.mapSimplex p rfl s) 0).1 heq
  have hp : J.rlp p := (fibration_iff _).1 inferInstance
  let : HasLiftingProperty (SSet.stdSimplex.δ.{u} (1 : Fin 2)) p :=
    AnodyneHomotopy.delta_anodyne 1 0 (by decide) p hp
  let sq : CommSq s.map (SSet.stdSimplex.δ (1 : Fin 2)) p r.map := ⟨r.δ_succ_map.symm⟩
  let v := SSet.yonedaEquiv (SSet.stdSimplex.δ (0 : Fin 2) ≫ sq.lift)
  have hv : p.app _ v = b := by
    have h : (SSet.stdSimplex.δ (0 : Fin 2) ≫ sq.lift) ≫ p = t.map := by
      rw [Category.assoc, sq.fac_right]
      exact r.δ_castSucc_map
    have h' : p.app _ v = SSet.yonedaEquiv t.map := by
      rw [← SSet.yonedaEquiv_comp]
      exact congrArg SSet.yonedaEquiv h
    exact h'.trans ((PtSimplex.equiv₀ (p.app _ e)).apply_symm_apply b)
  let tE : E.PtSimplex 0 e := (PtSimplex.equiv₀ e).symm v
  let rE : PtSimplex.RelStruct₀ tE s := {
    map := sq.lift
    δ_castSucc_map := by
      apply SSet.yonedaEquiv.injective
      exact ((PtSimplex.equiv₀ e).apply_symm_apply v).symm
    δ_succ_map := sq.fac_left
    δ_map_of_lt := by intro j hj; exact (Fin.not_lt_zero j hj).elim
    δ_map_of_gt := by intro j hj; exact (not_lt_of_ge (Fin.le_last j) hj).elim }
  refine ⟨v, hv, ?_⟩
  simpa only [s, tE, Equiv.apply_symm_apply] using
    (π₀.sound (PtSimplex.RelStruct₀.equiv₀ rE)).symm

/-- 概要：底の指定頂点に写る全空間の成分は、その頂点上の fiber の成分から来る。
方針：成分の代表を指定頂点上へ移し、その頂点を fiber の普遍性で持ち上げる。
規約：底の頂点が元の全空間の頂点の像であることを仮定しない。
使われ方：空の fiber も含む全空間の π₀ の比較の全射性。 -/
lemma fibration_componentFiber_exists {E B : SSet.{u}} [KanComplex E] [KanComplex B]
    (p : E ⟶ B) [Fibration p] (b : B _⦋0⦌) (a : π₀ E)
    (ha : mapπ₀ p a = π₀.mk b) :
    ∃ c : π₀ (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanFiber p b), mapπ₀ (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberι p b) c = a := by
  obtain ⟨e, rfl⟩ := π₀.mk_surjective a
  obtain ⟨e', he', hc⟩ := fibration_vertex_in_component p e b ha
  let k : (SSet.stdSimplex.obj ⦋0⦌ : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanFiber p b :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberLift p b (SSet.const e') (by simp only [const_comp, he'])
  refine ⟨π₀.mk (SSet.yonedaEquiv k), ?_⟩
  rw [mapπ₀_mk, ← SSet.yonedaEquiv_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberLift_ι, SSet.yonedaEquiv_const]
  exact hc

/-- 概要：任意の底の頂点上の fiber の成分の像は、その頂点に写る全空間の成分全体。
方針：順方向は辺の持ち上げ、逆方向は fiber の包含の定数合成を使う。
規約：fiber の参照頂点や非空性を仮定しない同値。
使われ方：Goerss–Jardine I §§7–8、Sp の引き戻しの零次数の比較。 -/
lemma fibration_componentFiber_exact {E B : SSet.{u}} [KanComplex E] [KanComplex B]
    (p : E ⟶ B) [Fibration p] (b : B _⦋0⦌) (a : π₀ E) :
    mapπ₀ p a = π₀.mk b ↔
      ∃ c : π₀ (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanFiber p b), mapπ₀ (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberι p b) c = a := by
  constructor
  · exact fibration_componentFiber_exists p b a
  · rintro ⟨c, rfl⟩
    obtain ⟨v, rfl⟩ := π₀.mk_surjective c
    rw [mapπ₀_mk, mapπ₀_mk, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiber_vertex_base]

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
