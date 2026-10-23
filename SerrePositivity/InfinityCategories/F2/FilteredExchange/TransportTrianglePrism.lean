module

public import SerrePositivity.InfinityCategories.F1.TransportRepresentationCompositionFamily

/-!
概要：元の coherent 三角形上の pointed な全持ち上げを保持する。
方針：二辺の prism と元の底の全二単体を構造の条件に含める。
規約：長辺の証拠の存在へ忘却しない。使われ方：指定三角形の比較同型の構成。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 概要：二つの元の prism と指定した底の全三角形を保持する持ち上げ。
方針：全射と三つの厳密な制限式を束ねる。
規約：元の二辺と二単体を型に含める。使われ方：指定比較の証明の選択での消失を防ぐ。 -/
structure TransportTrianglePrism {E F G B K : SSet.{u + 1}}
    {p : E ⟶ B} {q : F ⟶ B} {r : G ⟶ B}
    [LeftFibration p] [LeftFibration q] [LeftFibration r]
    {R : LeftTransportRepresentation p} {S : LeftTransportRepresentation q}
    {T : LeftTransportRepresentation r}
    {a : K ⟶ leftUnstraighteningTransformationSpace R.diagram S.diagram}
    {b : K ⟶ leftUnstraighteningTransformationSpace S.diagram T.diagram}
    {f : E ⊗ K ⟶ F} {g : F ⊗ K ⟶ G}
    (w : TransportRepresentationFamilyWitness R S a f)
    (v : TransportRepresentationFamilyWitness S T b g)
    (H : (Δ[2] : SSet.{u + 1}) ⊗ (B ⊗ K) ⟶ SpaceInfinity.{u}) where
  prism : (Δ[2] : SSet.{u + 1}) ⊗ (E ⊗ K) ⟶ PointedSpaceInfinity.{u}
  first : (stdSimplex.δ (2 : Fin 3) ▷ (E ⊗ K)) ≫ prism = w.leftPrism
  second : (stdSimplex.δ (0 : Fin 3) ▷ (E ⊗ K)) ≫ prism =
    (Δ[1] ◁ lift f (snd E K)) ≫ v.leftPrism
  projection : prism ≫ pointedSpaceProjection = (Δ[2] ◁ (p ▷ K)) ≫ H

end SerrePositivity.InfinityCategories.F2
