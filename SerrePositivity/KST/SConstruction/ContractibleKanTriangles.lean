module
public import SerrePositivity.KST.SConstruction.KanAssemblyMixedEndpoints
public import SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.BoundaryGluing

/-! # 可縮 Kan 複体の指定した三辺を埋める三角形
概要：任意の三頂点を結ぶ三本の辺を同時に保つ二単体を構成する。
方針：三辺を実際の二次境界へ貼り、全境界の充填を使う。
規約：合成の辺を新たに選び直さない。
使われ方：混合延長空間内の自然性ホモトピーの合成比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open SerrePositivity.InfinityCategories
open SerrePositivity.SimplicialModel
open scoped Simplicial

/-- 任意の三辺は二次境界の通常の面の互換条件を満たす。 -/
lemma triangleEdgeFaces_compatible {K : SSet.{u}} {x y z : K _⦋0⦌}
    (e : K.Edge x y) (f : K.Edge y z) (g : K.Edge x z) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.BoundaryGluing.StandardCompatible (n := 0)
      ![SSet.yonedaEquiv.symm f.edge, SSet.yonedaEquiv.symm g.edge,
        SSet.yonedaEquiv.symm e.edge] := by
  intro j k hjk
  fin_cases j <;> fin_cases k
  all_goals try { norm_num at hjk }
  all_goals dsimp
  all_goals apply SSet.yonedaEquiv.injective
  all_goals rw [stdSimplex.yonedaEquiv_δ_comp, stdSimplex.yonedaEquiv_δ_comp,
    Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  · exact f.tgt_eq.trans g.tgt_eq.symm
  · exact f.src_eq.trans e.tgt_eq.symm
  · exact g.src_eq.trans e.src_eq.symm

/-- 可縮 Kan 複体では指定済みの三辺を同時に回収する二単体が存在する。 -/
lemma contractibleKan_nonempty_compStruct {K : SSet.{u}} (hK : _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan K)
    {x y z : K _⦋0⦌} (e : K.Edge x y) (f : K.Edge y z) (g : K.Edge x z) :
    Nonempty (SSet.Edge.CompStruct e f g) := by
  let faces : Fin 3 → ((Δ[1] : SSet.{u}) ⟶ K) :=
    ![SSet.yonedaEquiv.symm f.edge, SSet.yonedaEquiv.symm g.edge,
      SSet.yonedaEquiv.symm e.edge]
  let q := _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.BoundaryGluing.standardDesc faces (triangleEdgeFaces_compatible e f g)
  obtain ⟨s, hs⟩ := hK 2 q
  have hf (i : Fin 3) : stdSimplex.δ i ≫ s = faces i := by
    rw [← boundary.ι_ι, Category.assoc, hs]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.BoundaryGluing.standardDesc_fac faces (triangleEdgeFaces_compatible e f g) i
  refine ⟨{
    simplex := SSet.yonedaEquiv s
    d₀ := by
      change K.δ 0 (SSet.yonedaEquiv s) = f.edge
      rw [← stdSimplex.yonedaEquiv_δ_comp, hf]
      exact SSet.yonedaEquiv.apply_symm_apply _
    d₁ := by
      change K.δ 1 (SSet.yonedaEquiv s) = g.edge
      rw [← stdSimplex.yonedaEquiv_δ_comp, hf]
      exact SSet.yonedaEquiv.apply_symm_apply _
    d₂ := by
      change K.δ 2 (SSet.yonedaEquiv s) = e.edge
      rw [← stdSimplex.yonedaEquiv_δ_comp, hf]
      exact SSet.yonedaEquiv.apply_symm_apply _ }⟩

end SerrePositivity.KST.SConstruction
