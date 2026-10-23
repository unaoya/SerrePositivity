module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.FunctorHomotopyPointedPrism
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.RelativeExtensionEndpointWitness

/-!
概要：元の始点・底・実終点を持つ実 prism を、一点パラメータ付きの同じ全族へ移す。
方針：射影で引き戻し、元の証拠の三つの厳密な式を保持する。
規約：元の全係数を保持。使われ方：F1 の既存の始域付き比較への同じ証拠の入力。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {B C : SSet.{u + 1}} {F G : B ⟶ SpaceInfinity.{u}}
  (H : SSet.Homotopy F G) (p : C ⟶ B) (s : C ⟶ leftUnstraightening F)
  (w : RelativeExtensionEndpointWitness pointedSpaceProjection
    ((Δ[1] ◁ p) ≫ functorSimplexDiagram (curry H.h)) (prismEndpoint 0 C)
    (s ≫ pullback.fst pointedSpaceProjection F) (prismEndpoint 1 C) G p)

/-- 元の実 prism を、そのまま一点パラメータへの射影で引き戻す。 -/
def functorHomotopySourceWrappedPrism :
    ((Δ[1] : SSet.{u + 1}) ⊗ C) ⊗ Δ[0] ⟶ PointedSpaceInfinity.{u} :=
  fst (Δ[1] ⊗ C) Δ[0] ≫ w.extension

/-- 元の実終点を、そのまま同じ一点パラメータへの射影で引き戻す。 -/
def functorHomotopySourceWrappedMap : C ⊗ (Δ[0] : SSet.{u + 1}) ⟶ leftUnstraightening G :=
  fst C Δ[0] ≫ w.endpoint

/-- 元の実終点の全族は、元の同じ底の射影を保持する。 -/
lemma functorHomotopySourceWrappedMap_projection :
    functorHomotopySourceWrappedMap H p s w ≫ leftUnstraighteningProjection G =
      fst C (Δ[0] : SSet.{u + 1}) ≫ p := by
  rw [functorHomotopySourceWrappedMap, Category.assoc]
  exact congrArg (fun z => fst C (Δ[0] : SSet.{u + 1}) ≫ z) w.endpoint_over

/-- 元の実 prism の同じ全始点を、一点パラメータでも厳密に保持する。 -/
lemma functorHomotopySourceWrappedPrism_source :
    (prismEndpoint 0 C ▷ (Δ[0] : SSet.{u + 1})) ≫
      functorHomotopySourceWrappedPrism H p s w =
      fst C Δ[0] ≫ s ≫ pullback.fst pointedSpaceProjection F := by
  rw [functorHomotopySourceWrappedPrism, ← Category.assoc, whiskerRight_fst,
    Category.assoc, w.initial]

/-- 元の実 prism の同じ全終点を、一点パラメータでも厳密に保持する。 -/
lemma functorHomotopySourceWrappedPrism_target :
    (prismEndpoint 1 C ▷ (Δ[0] : SSet.{u + 1})) ≫
      functorHomotopySourceWrappedPrism H p s w =
      functorHomotopySourceWrappedMap H p s w ≫ pullback.fst pointedSpaceProjection G := by
  rw [functorHomotopySourceWrappedPrism, ← Category.assoc, whiskerRight_fst,
    Category.assoc, w.evaluate]
  rfl

/-- 元の実 prism の同じ底を、元の指定変換の一点パラメータの全図式として保持。 -/
lemma functorHomotopySourceWrappedPrism_projection :
    functorHomotopySourceWrappedPrism H p s w ≫ pointedSpaceProjection =
      ((Δ[1] ◁ p) ▷ (Δ[0] : SSet.{u + 1})) ≫
      functorParameterizedPrism
        (intervalMappingUncurry (SSet.const (coherentVertexOfHomotopy H))) := by
  rw [functorHomotopySourceWrappedPrism, Category.assoc, w.over,
    coherentVertexOfHomotopy_parameterizedPrism]
  apply SSet.hom_ext
  intro n
  rfl

/-- 元の一点を代入すると、同じ実 prism を全係数上で厳密に回収する。 -/
lemma functorHomotopySourceWrappedPrism_restrict :
    prismParameterRestriction (lift (𝟙 C)
      (SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 1)))) ≫
      functorHomotopySourceWrappedPrism H p s w = w.extension := by
  apply SSet.hom_ext
  intro n
  rfl

end SerrePositivity.InfinityCategories.F2
