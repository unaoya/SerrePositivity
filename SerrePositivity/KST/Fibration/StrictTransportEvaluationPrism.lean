module
public import SerrePositivity.KST.Fibration.StrictTransportUnderEdge

/-! # 元の strict transport と両端 fiber 評価を結ぶ全 section 上の実 prism -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Fibration

/-- 元の恒等射評価を全空間へ含めると、同じ全 section の恒等射頂点での評価になる。 -/
theorem strictTransportEvaluate_ambient {I : Type u} [Category.{u} I] {E : SSet.{u}}
    (p : E ⟶ nerve I) (c : I) :
    kanCocartesianStrictTransportEvaluate p c ≫ vertexFiberι p (nerveVertex c) =
      cocartesianSectionEvaluate p (nerveMap (Under.forget c)) (nerveVertex (Under.mk (𝟙 c))) := by
  let a := nerveMap (Under.forget c)
  let v := (nerveEquiv (C := Under c)).symm (Under.mk (𝟙 c))
  have hv : v = nerveVertex (Under.mk (𝟙 c)) := ComposableArrows.ext₀ rfl
  have he : kanCocartesianStrictTransportEvaluate p c ≫ vertexFiberι p (nerveVertex c) =
      cocartesianSectionEvaluate p a v :=
    (Category.assoc _ _ _).trans
      (congrArg (fun m => kanCocartesianSectionsι p a ≫ m)
        (SerrePositivity.InfinityCategories.relativeFunctorEvaluate_ι p a v))
  exact he.trans (congrArg (cocartesianSectionEvaluate p a) hv)


/-- 同じ入力射に沿い、元の全 strict section を同時に評価する prism。 -/
def strictTransportEvaluationPrism {I : Type u} [Category.{u} I] {E : SSet.{u}}
    (p : E ⟶ nerve I) {c d : I} (f : c ⟶ d) :
    (Δ[1] : SSet.{u}) ⊗ kanCocartesianStrictTransport p c ⟶ E :=
  sectionEdgePrism p (nerveMap (Under.forget c)) (strictTransportUnderEdge f)

/-- 始点は元の strict section の同じ恒等射評価。 -/
theorem strictTransportEvaluationPrism_zero {I : Type u} [Category.{u} I] {E : SSet.{u}}
    (p : E ⟶ nerve I) {c d : I} (f : c ⟶ d) :
    prismEndpoint 0 _ ≫ strictTransportEvaluationPrism p f =
      kanCocartesianStrictTransportEvaluate p c ≫ vertexFiberι p (nerveVertex c) := by
  have he := sectionEdgePrism_endpoint p (nerveMap (Under.forget c))
    (strictTransportUnderEdge f) 0
  rw [strictTransportUnderEdge_zero] at he
  exact he.trans (strictTransportEvaluate_ambient p c).symm


/-- 終点は元の strict transport の後の、同じ終点の恒等射評価。 -/
theorem strictTransportEvaluationPrism_one {I : Type u} [Category.{u} I] {E : SSet.{u}}
    (p : E ⟶ nerve I) {c d : I} (f : c ⟶ d) :
    prismEndpoint 1 _ ≫ strictTransportEvaluationPrism p f =
      kanCocartesianStrictTransportMap p f ≫
        kanCocartesianStrictTransportEvaluate p d ≫ vertexFiberι p (nerveVertex d) := by
  have he := sectionEdgePrism_endpoint p (nerveMap (Under.forget c))
    (strictTransportUnderEdge f) 1
  rw [strictTransportUnderEdge_one] at he
  have ht := cocartesianSectionEvaluate_overPre p
    (Over.homMk (nerveUnderMap f) (nerveUnderMap_projection f) :
      Over.mk (nerveMap (Under.forget d)) ⟶ Over.mk (nerveMap (Under.forget c)))
    (nerveVertex (Under.mk (𝟙 d)))
  change kanCocartesianStrictTransportMap p f ≫
      cocartesianSectionEvaluate p (nerveMap (Under.forget d)) (nerveVertex (Under.mk (𝟙 d))) =
    cocartesianSectionEvaluate p (nerveMap (Under.forget c))
      ((nerveUnderMap f).app (Opposite.op ⦋0⦌) (nerveVertex (Under.mk (𝟙 d)))) at ht
  rw [kanCocartesianUnderMap_identity_vertex] at ht
  exact he.trans (ht.symm.trans (congrArg
    (fun m => kanCocartesianStrictTransportMap p f ≫ m)
    (strictTransportEvaluate_ambient p d).symm))


/-- 底の prism は、元の入力射そのものの定値パラメータ族。 -/
theorem strictTransportEvaluationPrism_projection
    {I : Type u} [Category.{u} I] {E : SSet.{u}}
    (p : E ⟶ nerve I) {c d : I} (f : c ⟶ d) :
    strictTransportEvaluationPrism p f ≫ p =
      fst (Δ[1] : SSet.{u}) _ ≫ yonedaEquiv.symm (nerve.edgeMk f).edge := by
  rw [strictTransportEvaluationPrism, sectionEdgePrism_projection,
    strictTransportUnderEdge_projection]
  rfl

end SerrePositivity.KST.Fibration
