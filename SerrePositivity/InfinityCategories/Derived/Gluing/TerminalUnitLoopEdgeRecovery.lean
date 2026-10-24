module
public import SerrePositivity.InfinityCategories.Derived.Gluing.TerminalUnitLoopClass
/-!
概要：厳密な終辺退化の基底辺を元の実閉路の端点から回収する。
方針：全正方形を閉路の零端へ制限し、単位錐の縮約と元の端点則を適用する。
規約：基底辺の追加同定を仮定せず、全時間の退化だけを用いる。
使われ方：第二単位面を正本の対角辺へ接続し、右単位閉路の零性を得る。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
lemma dgGluingTerminalUnitLoop_edge_recovery {K Z : SSet.{u}} {x y : Z _⦋0⦌}
    (b : K ⟶ intervalMappingSpace x y) (l : SSet.Homotopy b b)
    (e : (Δ[1] : SSet.{u}) ⊗ K ⟶ Z)
    (h : intervalMappingUncurry l.h =
      dgGluingTerminalUnitConeFamily K ≫ (stdSimplex.σ (1 : Fin 2) ▷ K) ≫ e) :
    e = intervalMappingUncurry b := by
  have hg : (Δ[1] ◁ (ι₀ : K ⟶ K ⊗ Δ[1])) ≫ dgGluingTerminalUnitConeFamily K ≫
      (stdSimplex.σ (1 : Fin 2) ▷ K) = 𝟙 _ := by
    rw [dgGluingTerminalUnitConeFamily_collapse]
    rfl
  have he := congrArg (fun m => (Δ[1] ◁ (ι₀ : K ⟶ K ⊗ Δ[1])) ≫ m) h
  rw [← intervalMappingUncurry_precomp, l.h₀, reassoc_of% hg] at he
  exact he.symm

lemma dgGluingTerminalUnitLoop_homMk_id_of_degenerate_triangle
    {K Z : SSet.{u}} {x y : Z _⦋0⦌}
    (b : K ⟶ intervalMappingSpace x y) (l : SSet.Homotopy b b)
    (e : (Δ[1] : SSet.{u}) ⊗ K ⟶ Z)
    (h : intervalMappingUncurry l.h =
      dgGluingTerminalUnitConeFamily K ≫ (stdSimplex.σ (1 : Fin 2) ▷ K) ≫ e) :
    Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy l) = 𝟙 _ := by
  apply dgGluingTerminalUnitLoop_homMk_id b l
  rw [h, dgGluingTerminalUnitLoop_edge_recovery b l e h]
end SerrePositivity.InfinityCategories
