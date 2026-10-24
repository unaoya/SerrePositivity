module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentTriangleStrictArrows
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.MorphismInitialTailHom
/-!
概要：最大化した三角形の最後辺上の初点固定 tail を、同じ strict な順序図式で読む。
方針：初点を保持した二つの添字前合成を順序図式へ移し、端点の表示を揃える。
規約：全次数・元の始点・元の最大 path の像を保持する。
使われ方：最後辺の全係数 prism の head を元の二辺へ正規化する。
-/

@[expose] public section
noncomputable section
open CategoryTheory SSet SimplicialThickening
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
open HomotopyLimits
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable (s : SpaceInfinity.{u} _⦋2⦌)
/-- 概要：最後辺を制限しても元の初点を保持する tail。
方針：最後面の添字を初点固定で前合成する。
規約：始点を中間点へ移さない。使われ方：Ncomp の実 head の計算。 -/
def coherentTriangleLastTail {n : ℕ} (α : ⦋n⦌ ⟶ ⦋1⦌) :
    fixedInitialSimplex (s.obj ⟨ULift.up 0⟩) n :=
  fixedInitialSimplexReindex _ (α ≫ SimplexCategory.δ 0)
    (⟨coherentConeTailExtension (coherentSimplexMaximalization s), rfl⟩ :
      fixedInitialSimplex (s.obj ⟨ULift.up 0⟩) 2)
/-- 概要：同じ tail は同じ strict な順序図式の表示。
方針：最大化の表示と二つの前合成則を使う。
規約：豊穣 Hom 全体の等式。使われ方：全次数の head と tail の計算。 -/
lemma coherentTriangleLastTail_eq_order {n : ℕ} (α : ⦋n⦌ ⟶ ⦋1⦌) :
    (coherentTriangleLastTail s α).val = enrichedFunctorOfOrderDiagram
      ((OrderHom.uliftMap.{0, 0, u, u}
        (prependOrderHom (α ≫ SimplexCategory.δ 0).toOrderHom)).toFunctor ⋙
        (OrderHom.uliftMap.{0, 0, u, u} (coherentTailRetraction 2)).toFunctor ⋙ coherentSimplexStrictDiagram s) := by
  change (SimplicialThickening.functor _).comp SSet
    ((SimplicialThickening.functor _).comp SSet (coherentSimplexMaximalization s)) = _
  rw [coherentSimplexMaximalization_eq_strictDiagram s,
    enrichedFunctorOfOrderDiagram_precomp, enrichedFunctorOfOrderDiagram_precomp]

/-- 概要：初点を固定して最後辺の各頂点を送る添字写像。
方針：初点の追加と tail の取り出しを合成する。
規約：元の初点は零番目。使われ方：実単体の端点表示。 -/
def coherentTriangleLastTailOrder {n : ℕ} (α : ⦋n⦌ ⟶ ⦋1⦌) :
    ULift.{u} (Fin (n + 2)) →o ULift.{u} (Fin 3) :=
  (OrderHom.uliftMap.{0, 0, u, u} (coherentTailRetraction 2)).comp
    (OrderHom.uliftMap.{0, 0, u, u} (prependOrderHom (α ≫ SimplexCategory.δ 0).toOrderHom))
/-- 概要：端点表示を揃えた tail の Hom は同じ strict な射の定値射。
方針：順序図式の表示から、薄い圏の射の移送則を適用する。
規約：元の path 全体を保持。使われ方：最後辺の head の二時刻計算。 -/
lemma coherentTriangleLastTail_map_labels {n : ℕ} (α : ⦋n⦌ ⟶ ⦋1⦌) (i j : ULift.{u} (Fin (n + 2)))
    (hij : i ≤ j) (k l : ULift.{u} (Fin 3))
    (hk : coherentTriangleLastTailOrder α i = k)
    (hl : coherentTriangleLastTailOrder α j = l) (hkl : k ≤ l) :
    (coherentTriangleLastTail s α).val.map ⟨i⟩ ⟨j⟩ ≫
      eqToHom (congrArg₂ SimplicialCategory.sHom
        (congrArg (coherentSimplexStrictDiagram s).obj hk)
        (congrArg (coherentSimplexStrictDiagram s).obj hl)) =
      SSet.const (SimplicialCategory.homEquiv' _ _
        ((coherentSimplexStrictDiagram s).map (homOfLE hkl))) := by
  have hm := eq_of_heq (enrichedFunctor_map_heq
    (coherentTriangleLastTail_eq_order s α) ⟨i⟩ ⟨j⟩)
  rw [hm]
  change orderDiagramEnrichedHom
    ((coherentTriangleLastTailOrder α).toFunctor ⋙ coherentSimplexStrictDiagram s) ⟨i⟩ ⟨j⟩ ≫ _ = _
  rw [orderDiagramEnrichedHom_const _ _ _ hij, SSet.const_comp]
  apply congrArg SSet.const
  change (eqToHom (congrArg₂ SimplicialCategory.sHom
    (congrArg (coherentSimplexStrictDiagram s).obj hk)
    (congrArg (coherentSimplexStrictDiagram s).obj hl))).app (Opposite.op ⦋0⦌)
      (SimplicialCategory.homEquiv' _ _ ((coherentSimplexStrictDiagram s).map
        (homOfLE ((coherentTriangleLastTailOrder α).monotone hij)))) = _
  rw [simplicialHomVertex_transport (congrArg (coherentSimplexStrictDiagram s).obj hk)
    (congrArg (coherentSimplexStrictDiagram s).obj hl)]
  apply congrArg (SimplicialCategory.homEquiv' _ _)
  exact functor_map_transport_of_isThin (coherentSimplexStrictDiagram s) hk hl _ (homOfLE hkl)
end SerrePositivity.InfinityCategories.F2
