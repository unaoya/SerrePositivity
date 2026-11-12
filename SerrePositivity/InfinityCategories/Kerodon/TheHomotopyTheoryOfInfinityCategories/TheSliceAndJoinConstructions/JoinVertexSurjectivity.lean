module
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.JoinBoundary

/-! # join の頂点の被覆

概要：頂点上全射な二写像の join は頂点上全射で、正次元境界との join の包含もそうである。
方針：join の零単体の二つの切断と標準単体の全頂点が境界にあることを使う。
規約：HTT §1.2.8。使われ方：充満部分圏へ境界充填を持ち上げる際の全頂点の回収。

対応節は Kerodon 4.3（Tag 015M）。
-/

@[expose] public section
noncomputable section

universe u

namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions

open CategoryTheory Opposite
open scoped _root_.Simplicial

/-- 概要：二写像が頂点上全射なら、その join も頂点上全射。
方針：join の零単体の切断は零か一であり、対応する因子の全射性を使う。
規約：HTT §1.2.8。使われ方：境界との join の頂点の被覆。 -/
lemma joinMap_vertices_surjective {K K' L L' : SSet.{u}} (f : K ⟶ K') (g : L ⟶ L')
    (hf : Function.Surjective (f.app (op ⦋0⦌)))
    (hg : Function.Surjective (g.app (op ⦋0⦌))) :
    Function.Surjective ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap f g).app (op ⦋0⦌)) := by
  rintro ⟨c, x, y⟩
  fin_cases c
  · obtain ⟨y', hy⟩ := hg y
    refine ⟨⟨0, PUnit.unit, y'⟩, ?_⟩
    refine _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.Simplex.ext _ _ ?_ ?_ ?_
    · rfl
    · exact @Subsingleton.elim PUnit inferInstance _ _
    · exact hy
  · obtain ⟨x', hx⟩ := hf x
    refine ⟨⟨1, x', PUnit.unit⟩, ?_⟩
    refine _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.Simplex.ext _ _ ?_ ?_ ?_
    · rfl
    · exact hx
    · exact @Subsingleton.elim PUnit inferInstance _ _

/-- 概要：正次元標準単体の境界の包含は頂点上全射。
方針：標準単体の零単体を頂点番号で表示し、全頂点が境界に属することを使う。
規約：HTT §1.2.12。使われ方：自由因子の境界が充填に使う全対象を含むこと。 -/
lemma boundary_vertices_surjective (n : ℕ) :
    Function.Surjective ((SSet.boundary (n + 1)).ι.app (op ⦋0⦌) :
      (SSet.boundary (n + 1) : SSet.{u}) _⦋0⦌ → (Δ[n + 1] : SSet.{u}) _⦋0⦌) := by
  intro z
  refine ⟨⟨z, ?_⟩, rfl⟩
  rw [← SSet.stdSimplex.obj₀Equiv.symm_apply_apply z]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.vertex_mem_boundary n (SSet.stdSimplex.obj₀Equiv z)

/-- 概要：正次元の境界包含と恒等射の join は頂点上全射。
方針：境界の頂点全射性と恒等射の全射性を join の全射性へ渡す。
規約：HTT §1.2.13。使われ方：slice の境界充填の像が充満部分圏に留まること。 -/
lemma boundaryJoin_vertices_surjective (n : ℕ) (K : SSet.{u}) :
    Function.Surjective ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (SSet.boundary (n + 1)).ι (𝟙 K)).app (op ⦋0⦌)) :=
  joinMap_vertices_surjective _ _ (boundary_vertices_surjective n) (fun z => ⟨z, rfl⟩)

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
