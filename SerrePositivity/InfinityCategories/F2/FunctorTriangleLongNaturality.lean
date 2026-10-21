module

public import SerrePositivity.InfinityCategories.F2.FunctorTriangleLongEndpointComparison
public import SerrePositivity.InfinityCategories.F2.FunctorTriangleInitialNativeIdentity
public import SerrePositivity.InfinityCategories.F2.FunctorTrianglePointedLongWitness

/-!
概要：元の全三角形の長辺への指定自然性から、同じ指定始域比較と全終点比較の式を得る。
方針：固定始点の恒等性と同じ全終点評価を使い、元の指定長辺の証拠も回収する。
規約：全係数・元の指定値を保持。使われ方：元の指定三角形比較の最終照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {B C : SSet.{u + 1}} {F G J : B ⟶ SpaceInfinity.{u}}
  {a : SSet.Homotopy F G} {b : SSet.Homotopy G J} {c : SSet.Homotopy F J}
  {T : FunctorCompositionTriangle a b c} {p : C ⟶ B} {s : C ⟶ leftUnstraightening F}
  (w : FunctorTrianglePointedWitness T p s) (hi : s ≫ leftUnstraighteningProjection F = p)
local notation "z" => functorTrianglePointedCanonicalWitness T p s hi
local notation "V" => coherentTriangleOfFunctorTriangle T

/-- 元の長辺の指定自然性は、元の二つの指定始域比較と同じ全終点比較を結ぶ。 -/
lemma FunctorTrianglePointedWitness.long_specified_naturality :
    functorHomotopySourceEndpointIso c p s hi (z).longWitness =
      functorHomotopySourceEndpointIso c p s hi w.longWitness ≪≫ w.endpointComparison hi := by
  have hs := functorHomotopyPrismSpecified_naturality c p s s hi hi w.longWitness
    (z).longWitness (w.longPrismComparison hi)
  change w.longNativeComparison hi ≪≫
    functorHomotopySourceEndpointIso c p s hi (z).longWitness =
    functorHomotopySourceEndpointIso c p s hi w.longWitness ≪≫ w.longActualComparison hi at hs
  rw [w.longNativeComparison_eq_refl hi, w.longActualComparison_eq_endpoint hi] at hs
  simpa only [Iso.refl_trans] using hs

/-- 元の指定三角形の実長辺は、元の指定比較に使った同じ長辺証拠の実制限そのもの。 -/
lemma functorTriangleCanonical_long_extension :
    (z).longWitness.extension = prismParameterRestriction
      (lift s (SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 1)))) ≫
      (unstraighteningMappingTriangleLongWitness F G J
        (SSet.const (coherentVertexOfHomotopy a)) (SSet.const (coherentVertexOfHomotopy b))
        (SSet.const (coherentVertexOfHomotopy c)) (V).diagram (V).first (V).second
          (V).long).prism := by
  calc
    _ = (Δ[1] ◁ s) ≫ (stdSimplex.δ (1 : Fin 3) ▷ leftUnstraightening F) ≫
        functorTrianglePointedLift T := by
      apply SSet.hom_ext
      intro n
      rfl
    _ = _ := functorTrianglePointedLift_long T s

end SerrePositivity.InfinityCategories.F2
