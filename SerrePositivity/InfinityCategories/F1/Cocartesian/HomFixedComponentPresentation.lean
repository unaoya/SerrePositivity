module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.HomFixedComponentCurry

/-!
概要：実際の固定成分 fiber の prism 表示の普遍性と、元の Hom 作用との整合性。
方針：構成した両逆で三辺固定の族を一意に回収し、元の比較の包含公式を展開する。
規約：別の正方形や独立な Hom 同値を選ばない。
使われ方：一次元分類の Hom 比較の、同じ三角形での検証。
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
local notation "B" => (cocartesianHomDiagramBase C)
local notation "D₀" => (qCatDiagramCoherentNerve (cocartesianTransportDiagramValueFunctor F))
local notation "D₁" => (qCatDiagramCoherentNerve (cocartesianTransportDiagramValueFunctor G))

/-- 三辺を固定した全パラメーターの prism は、同じ実際の fiber の一意な族を表す。 -/
lemma existsUnique_cocartesianHomFixedComponentPrism {T : SSet.{u + 1}}
    (v : (intervalMappingSpace (coherentNerveVertex (cocartesianTransportDiagramValue F c))
      (coherentNerveVertex (cocartesianTransportDiagramValue G c))) _⦋0⦌)
    (H : ((Δ[1] : SSet.{u + 1}) ⊗ B) ⊗ T ⟶ CatInfinity.{u})
    (h₀ : (prismEndpoint 0 B ▷ T) ≫ H = fst B T ≫ D₀)
    (h₁ : (prismEndpoint 1 B ▷ T) ≫ H = fst B T ≫ D₁)
    (hc : (lift (𝟙 (Δ[1] : SSet.{u + 1}))
      (SSet.const (ULift.up (nerveVertex c))) ▷ T) ≫ H =
        intervalMappingUncurry (SSet.const v : T ⟶ _)) :
    ∃! f : T ⟶ vertexFiber (cocartesianHomIntervalEvaluation F G c) v,
      cocartesianHomFixedComponentPrism F G c v f = H := by
  refine ⟨cocartesianHomFixedComponentCurry F G c v H h₀ h₁ hc,
    cocartesianHomFixedComponentPrism_curry F G c v H h₀ h₁ hc, ?_⟩
  intro f hf
  apply cocartesianHomFixedComponentPrism_injective F G c v
  rw [hf, cocartesianHomFixedComponentPrism_curry]

/-- 元の固定成分比較の prism は、元の全 Hom 作用を同じ fiber へ制限した prism そのもの。 -/
lemma cocartesianHomFixedComponentComparison_prism
    (b : ((SSet.uliftFunctor.{u + 1, u}).obj
      (SimplicialCategory.sHom (cocartesianTransportDiagramValue F c)
        (cocartesianTransportDiagramValue G c))) _⦋0⦌) :
    cocartesianHomFixedComponentPrism F G c
      ((coherentHomIntervalComparison (cocartesianTransportDiagramValue F c)
        (cocartesianTransportDiagramValue G c)).app _ b)
      (cocartesianHomFixedComponentComparison F G c b) =
    intervalFunctorHomPrism
      (vertexFiberι (cocartesianHomSourceComponent F G c) b ≫
        cocartesianTransportDiagramHomInterval F G) := by
  unfold cocartesianHomFixedComponentPrism
  rw [cocartesianHomFixedComponentComparison_ι]

end SerrePositivity.InfinityCategories
