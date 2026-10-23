module
public import SerrePositivity.InfinityCategories.F1.Cocartesian.SectionCoreLift
public import SerrePositivity.InfinityCategories.F1.RelativeFunctorActionEvaluation
public import SerrePositivity.InfinityCategories.F1.Cocartesian.Transport

/-! # 元の section の全族を指定した辺で評価する厳密な prism -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Fibration

/-- 同じ全 section を、指定した始域の実辺に沿って同時に評価する。 -/
def sectionEdgePrism {A E B : SSet.{u}} (p : E ⟶ B) (a : A ⟶ B) (e : Δ[1] ⟶ A) :
    (Δ[1] : SSet.{u}) ⊗ kanCocartesianSections p a ⟶ E :=
  uncurry (kanCocartesianSectionsι p a ≫
    vertexFiberι ((ihom A).map p) (functorVertex a) ≫ (pre e).app E)

/-- 元の両端評価は、全 section 上の同じ prism の端点そのもの。 -/
theorem sectionEdgePrism_endpoint {A E B : SSet.{u}} (p : E ⟶ B) (a : A ⟶ B)
    (e : Δ[1] ⟶ A) (j : Fin 2) :
    prismEndpoint j _ ≫ sectionEdgePrism p a e =
      cocartesianSectionEvaluate p a
        (e.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm j)) := by
  rw [sectionEdgePrism, ← curry_evaluateFunctorAt_interval, curry_uncurry]
  unfold cocartesianSectionEvaluate
  rw [Category.assoc, Category.assoc, evaluateFunctorAt_pre]

/-- 同じ prism を底へ送ると、指定辺の底像の定値パラメータ族となる。 -/
theorem sectionEdgePrism_projection {A E B : SSet.{u}} (p : E ⟶ B) (a : A ⟶ B)
    (e : Δ[1] ⟶ A) :
    sectionEdgePrism p a e ≫ p = fst (Δ[1] : SSet.{u}) _ ≫ e ≫ a := by
  unfold sectionEdgePrism
  rw [← uncurry_natural_right]
  have hp : (kanCocartesianSectionsι p a ≫
      vertexFiberι ((ihom A).map p) (functorVertex a) ≫ (pre e).app E) ≫
        (ihom (Δ[1] : SSet.{u})).map p =
      SSet.const (functorVertex (e ≫ a)) := by
    rw [Category.assoc, Category.assoc, ← (pre e).naturality p,
      ← Category.assoc (vertexFiberι _ _), vertexFiberι_comp,
      SSet.const_comp, SSet.comp_const]
    rfl
  rw [hp, uncurry_const_functorVertex]

end SerrePositivity.KST.Fibration
