module

public import SerrePositivity.InfinityCategories.F1.CocartesianHomFixedComponentPrism

/-!
概要：三辺を固定した実際の prism を、分類先の同じ固定成分 fiber の族に戻す。
方針：両端固定の curry と指定点での評価の等式で fiber に持ち上げる。
規約：全パラメーターで元の prism を回収し、族の一意性も保つ。
使われ方：一次元セルの分類先の Hom fiber の実際の正方形表示。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

variable {C : Type u} [Category.{u} C] (F G : CocartesianTransportDiagramCategory C) (c : C)
variable (v : (intervalMappingSpace (coherentNerveVertex (cocartesianTransportDiagramValue F c))
  (coherentNerveVertex (cocartesianTransportDiagramValue G c))) _⦋0⦌)
local notation "B" => (cocartesianHomDiagramBase C)
local notation "D₀" => (qCatDiagramCoherentNerve (cocartesianTransportDiagramValueFunctor F))
local notation "D₁" => (qCatDiagramCoherentNerve (cocartesianTransportDiagramValueFunctor G))
local notation "p" => (cocartesianHomIntervalEvaluation F G c)
local notation "E" => (vertexFiber p v)

/-- 元の三辺固定の prism を、実際の固定成分 fiber の族へ戻す。 -/
def cocartesianHomFixedComponentCurry {T : SSet.{u + 1}}
    (H : ((Δ[1] : SSet.{u + 1}) ⊗ B) ⊗ T ⟶ CatInfinity.{u})
    (h₀ : (prismEndpoint 0 B ▷ T) ≫ H = fst B T ≫ D₀)
    (h₁ : (prismEndpoint 1 B ▷ T) ≫ H = fst B T ≫ D₁)
    (hc : (lift (𝟙 (Δ[1] : SSet.{u + 1}))
      (SSet.const (ULift.up (nerveVertex c))) ▷ T) ≫ H =
        intervalMappingUncurry (SSet.const v : T ⟶ _)) : T ⟶ E :=
  vertexFiberLift p v (intervalFunctorHomPrismCurry H h₀ h₁) (by
    apply intervalMappingUncurry_injective
    let f := intervalFunctorHomPrismCurry H h₀ h₁
    have h := intervalFunctorHomPrism_evaluateOfEq f (ULift.up (nerveVertex c))
      (x := coherentNerveVertex (cocartesianTransportDiagramValue F c))
      (y := coherentNerveVertex (cocartesianTransportDiagramValue G c))
      (by simpa only
        [evaluateFunctorAt_functorVertex, cocartesianTransportDiagramValueFunctor] using
        qCatDiagramCoherentNerve_vertex (cocartesianTransportDiagramValueFunctor F) c)
      (by simpa only
        [evaluateFunctorAt_functorVertex, cocartesianTransportDiagramValueFunctor] using
        qCatDiagramCoherentNerve_vertex (cocartesianTransportDiagramValueFunctor G) c)
    change _ = intervalMappingUncurry (f ≫ p) at h
    rw [show intervalFunctorHomPrism f = H from intervalFunctorHomPrism_curry H h₀ h₁,
      hc] at h
    exact h.symm)

/-- 三辺固定の prism を実際の fiber に戻して展開すると、元の prism を厳密に回収する。 -/
lemma cocartesianHomFixedComponentPrism_curry {T : SSet.{u + 1}}
    (H : ((Δ[1] : SSet.{u + 1}) ⊗ B) ⊗ T ⟶ CatInfinity.{u})
    (h₀ : (prismEndpoint 0 B ▷ T) ≫ H = fst B T ≫ D₀)
    (h₁ : (prismEndpoint 1 B ▷ T) ≫ H = fst B T ≫ D₁)
    (hc : (lift (𝟙 (Δ[1] : SSet.{u + 1}))
      (SSet.const (ULift.up (nerveVertex c))) ▷ T) ≫ H =
        intervalMappingUncurry (SSet.const v : T ⟶ _)) :
    cocartesianHomFixedComponentPrism F G c v
      (cocartesianHomFixedComponentCurry F G c v H h₀ h₁ hc) = H := by
  unfold cocartesianHomFixedComponentPrism cocartesianHomFixedComponentCurry
  rw [vertexFiberLift_ι, intervalFunctorHomPrism_curry]

/-- 元の固定成分 fiber の族を展開して戻すと、同じ族を厳密に回収する。 -/
lemma cocartesianHomFixedComponentCurry_prism {T : SSet.{u + 1}} (f : T ⟶ E) :
    cocartesianHomFixedComponentCurry F G c v (cocartesianHomFixedComponentPrism F G c v f)
      (cocartesianHomFixedComponentPrism_zero F G c v f)
      (cocartesianHomFixedComponentPrism_one F G c v f)
      (cocartesianHomFixedComponentPrism_at F G c v f) = f := by
  apply cocartesianHomFixedComponentPrism_injective F G c v
  exact cocartesianHomFixedComponentPrism_curry F G c v _ _ _ _

end SerrePositivity.InfinityCategories
