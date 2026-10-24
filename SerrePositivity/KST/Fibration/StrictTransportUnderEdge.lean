module
public import SerrePositivity.KST.Fibration.SectionEdgePrism
public import SerrePositivity.InfinityCategories.F1B.Fibrations.CocartesianStrictTransport
public import SerrePositivity.KST.LocalizingInvariants.IntervalPostcompositionFamily

/-! # strict transport の元の undercategory 内の恒等射からの辺 -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration

/-- 元の undercategory で、恒等射から入力された射へ向かう実辺。 -/
def strictTransportUnderEdge {I : Type u} [Category.{u} I] {c d : I} (f : c ⟶ d) :
    (Δ[1] : SSet.{u}) ⟶ nerve (Under c) :=
  yonedaEquiv.symm (nerve.edgeMk (Under.homMk f (by simp) :
    Under.mk (𝟙 c) ⟶ Under.mk f)).edge

/-- 始点は元の恒等射の頂点。 -/
theorem strictTransportUnderEdge_zero {I : Type u} [Category.{u} I] {c d : I} (f : c ⟶ d) :
    (strictTransportUnderEdge f).app (Opposite.op ⦋0⦌)
        (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) = nerveVertex (Under.mk (𝟙 c)) := by
  rw [← intervalMap_source, strictTransportUnderEdge, Equiv.apply_symm_apply]
  exact ComposableArrows.ext₀ rfl

/-- 終点は元の入力射の under 頂点。 -/
theorem strictTransportUnderEdge_one {I : Type u} [Category.{u} I] {c d : I} (f : c ⟶ d) :
    (strictTransportUnderEdge f).app (Opposite.op ⦋0⦌)
        (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) = nerveVertex (Under.mk f) := by
  rw [← intervalMap_target, strictTransportUnderEdge, Equiv.apply_symm_apply]
  exact ComposableArrows.ext₀ rfl

/-- 底の射は、元の入力射そのもの。 -/
theorem strictTransportUnderEdge_projection {I : Type u} [Category.{u} I]
    {c d : I} (f : c ⟶ d) :
    strictTransportUnderEdge f ≫ nerveMap (Under.forget c) =
      yonedaEquiv.symm (nerve.edgeMk f).edge := by
  apply yonedaEquiv.injective
  rw [yonedaEquiv_comp, strictTransportUnderEdge, Equiv.apply_symm_apply,
    Equiv.apply_symm_apply]
  rw [nerve.edgeMk_edge, nerve.edgeMk_edge, nerveMap_app_mk₁]
  rfl

/-- strict transport の前合成は、元の終点の恒等射を入力射へ送る。 -/
theorem kanCocartesianUnderMap_identity_vertex {I : Type u} [Category.{u} I]
    {c d : I} (f : c ⟶ d) :
    (nerveUnderMap f).app (Opposite.op ⦋0⦌) (nerveVertex (Under.mk (𝟙 d))) =
      nerveVertex (Under.mk f) := by
  rw [nerveUnderMap, nerveVertex, nerveMap_app_mk₀]
  change nerveVertex (Under.mk (f ≫ 𝟙 d)) = _
  rw [Category.comp_id]

end SerrePositivity.KST.Fibration
