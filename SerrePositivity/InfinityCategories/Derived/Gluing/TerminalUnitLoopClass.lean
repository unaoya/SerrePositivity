module
public import SerrePositivity.InfinityCategories.Derived.Gluing.UnitCapUnitLoopDomains
public import SerrePositivity.InfinityCategories.Derived.Gluing.RelativeHomotopyEdgeClass
public import SerrePositivity.InfinityCategories.F1B.Homotopy.HomotopyWhiskering
/-! # 終辺の厳密単位退化から実単位閉路の零性

概要：終辺単位三角形が全体で退化する場合、同じ正方形の実閉路は恒等射の類を持つ。
方針：全正方形の退化を区間写像空間へ戻し、元実閉路の辺を比較する。
規約：全時間の等式を使い、端点一致だけでは代用しない。
使われ方：D の第二入力の厳密単位則を実六片の右単位辺へ供給する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
lemma dgGluingTerminalUnitConeFamily_degenerate_evaluate {K Z : SSet.{u}} {x y : Z _⦋0⦌}
    (b : K ⟶ intervalMappingSpace x y) :
    dgGluingTerminalUnitConeFamily K ≫ (stdSimplex.σ (1 : Fin 2) ▷ K) ≫
      intervalMappingUncurry b = intervalMappingUncurry (functorHomotopyRefl b).h := by
  rw [← Category.assoc, dgGluingTerminalUnitConeFamily_collapse,
    ← intervalMappingUncurry_precomp]
  rfl

lemma dgGluingTerminalUnitLoop_homMk_id {K Z : SSet.{u}} {x y : Z _⦋0⦌}
    (b : K ⟶ intervalMappingSpace x y) (l : SSet.Homotopy b b)
    (h : intervalMappingUncurry l.h =
      dgGluingTerminalUnitConeFamily K ≫ (stdSimplex.σ (1 : Fin 2) ▷ K) ≫
        intervalMappingUncurry b) :
    Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy l) = 𝟙 _ := by
  have he : l.h = (functorHomotopyRefl b).h :=
    intervalMappingUncurry_injective _ _
      (h.trans (dgGluingTerminalUnitConeFamily_degenerate_evaluate b))
  have he' : functorEdgeOfSimplicialHomotopy l =
      functorEdgeOfSimplicialHomotopy (functorHomotopyRefl b) := by
    apply Truncated.Edge.ext
    exact congrArg (fun f => SSet.yonedaEquiv (curry f)) he
  rw [he', functorHomotopyRefl_hom]
  rfl
end SerrePositivity.InfinityCategories
