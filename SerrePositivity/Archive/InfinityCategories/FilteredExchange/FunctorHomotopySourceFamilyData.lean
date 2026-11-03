module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.FunctorHomotopySourceComparison

/-!
概要：同じ実 prism の一点パラメータ族の初期・終端条件と、元の指定比較の実データ。
方針：元の証拠の三条件と一点代入の厳密な回収を使う。
規約：全実延長と実終点を保持。使われ方：F1 の指定成分と元の長辺比較の同定。
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
local notation "t" => SSet.const (coherentVertexOfHomotopy H)
local notation "d" => ((Δ[1] ◁ p) ▷ Δ[0]) ≫ functorParameterizedPrism (intervalMappingUncurry t)
local notation "v" => fst C Δ[0] ≫ s ≫ pullback.fst pointedSpaceProjection F

include w in
/-- 元の一点パラメータ族の同じ全初期値は、同じ全底を被覆する。 -/
lemma functorHomotopySourceFamily_initial :
    v ≫ pointedSpaceProjection = (prismEndpoint 0 C ▷ (Δ[0] : SSet.{u + 1})) ≫ d := by
  rw [← functorHomotopySourceWrappedPrism_source H p s w, Category.assoc,
    functorHomotopySourceWrappedPrism_projection H p s w]

include w in
/-- 元の一点パラメータ族の底の終点は、同じ元の標的図式。 -/
lemma functorHomotopySourceFamily_endpoint :
    (prismEndpoint 1 C ▷ (Δ[0] : SSet.{u + 1})) ≫ d = (fst C Δ[0] ≫ p) ≫ G := by
  rw [← functorHomotopySourceWrappedPrism_projection H p s w, ← Category.assoc,
    functorHomotopySourceWrappedPrism_target H p s w, Category.assoc, pullback.condition,
    ← Category.assoc]
  exact congrArg (fun z => z ≫ G) (functorHomotopySourceWrappedMap_projection H p s w)

include w in
/-- 元の実 prism の底は、指定比較の一点制限の底そのもの。 -/
lemma functorHomotopySourceFamily_base_restrict :
    (Δ[1] ◁ p) ≫ functorSimplexDiagram (curry H.h) =
      prismParameterRestriction (lift (𝟙 C)
        (SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 1)))) ≫ d := by
  have hr := functorHomotopySourceWrappedPrism_restrict H p s w
  rw [← w.over, ← hr, Category.assoc, functorHomotopySourceWrappedPrism_projection]

/-- 同じ元の全初期値は、元の指定比較の一点制限の初期値そのもの。 -/
lemma functorHomotopySourceFamily_initial_restrict :
    s ≫ pullback.fst pointedSpaceProjection F =
      lift (𝟙 C) (SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 1))) ≫ v := by
  simp only [lift_fst_assoc, Category.id_comp]

/-- 同じ元の終点底は、元の指定比較の一点制限の終点底そのもの。 -/
lemma functorHomotopySourceFamily_apex_restrict :
    p = lift (𝟙 C) (SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 1))) ≫
      (fst C (Δ[0] : SSet.{u + 1}) ≫ p) := by
  simp only [lift_fst_assoc, Category.id_comp]

end SerrePositivity.InfinityCategories.F2
