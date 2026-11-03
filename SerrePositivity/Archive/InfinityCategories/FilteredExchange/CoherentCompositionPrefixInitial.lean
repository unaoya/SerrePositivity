module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentInitialEdgeInterval
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentPrefixConeConstant
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentCompositionTetrahedronFirstEdge

/-!
概要：比較三単体の零面の初点で prefix 円柱は元の恒等 cone に固定される。
方針：初点の tail を元の初二頂点へ制限し、その実恒等辺を回収する。
規約：全時刻と元の実辺を保持する。
使われ方：同じ初点固定延長空間の指定比較との一致。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory SimplicialThickening SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 元の最初の二頂点への豊穣制限は比較三単体の実恒等辺。 -/
lemma coherentCompositionTetrahedron_initial_edge_restriction
    {C : Type v} [Category.{u} C] [SimplicialCategory C]
    (s : (SimplicialNerve C) _⦋2⦌) :
    (SimplicialThickening.functor coherentInitialEdgeObjects).comp SSet
      (coherentCompositionTetrahedron s) =
        PinchedHom.constant (coherentNerveVertex (s.obj ⟨ULift.up 0⟩)) 1 := by
  have hb : coherentInitialEdgeObjects.{u} =
      (SimplexCategory.δ (3 : Fin 4)).toOrderHom.uliftMap.comp
        (SimplexCategory.δ (2 : Fin 3)).toOrderHom.uliftMap := by
    ext i
    rcases i with ⟨i⟩
    fin_cases i <;> rfl
  rw [hb, SimplicialThickening.functor_comp]
  exact coherentCompositionTetrahedron_first_edge s

/-- 全時刻において初点の prefix 単体は元の恒等 cone。 -/
lemma coherentCompositionPrefix_initial
    {C : Type v} [Category.{u} C] [SimplicialCategory C] {m : ℕ}
    (s : (SimplicialNerve C) _⦋2⦌) (t : Fin (m + 1) →o Fin 2) :
    coherentPrefixConeSimplex (coherentCompositionTetrahedron s)
      (OrderHom.const _ (0 : Fin 3)) t =
        PinchedHom.constant (coherentNerveVertex (s.obj ⟨ULift.up 0⟩)) (m + 1) := by
  have ha : (prependOrderHom (OrderHom.const (Fin (m + 1)) (0 : Fin 3))).uliftMap =
      coherentInitialEdgeObjects.{u}.comp
        (prependOrderHom (OrderHom.const (Fin (m + 1)) (0 : Fin 1))).uliftMap := by
    ext i
    rcases i with ⟨i⟩
    induction i using Fin.cases with
    | zero => rfl
    | succ i => rfl
  unfold coherentPrefixConeSimplex
  rw [ha, coherentPrefixPathDeformationEnriched_target_map _ _ _
    coherentInitialEdgeObjects_interval]
  change (coherentPrefixPathDeformationEnriched _ _).comp SSet
    ((SimplicialThickening.functor coherentInitialEdgeObjects).comp SSet
      (coherentCompositionTetrahedron s)) = _
  rw [coherentCompositionTetrahedron_initial_edge_restriction]
  exact coherentPrefixConeSimplex_constant _ (OrderHom.const _ (0 : Fin 1)) t

end SerrePositivity.InfinityCategories.F2
