module

public import SerrePositivity.InfinityCategories.F2.TransportTrianglePrismChoice

/-!
概要：保持した元の全三角形の長辺から合成の pointed な証拠を取り出す。
方針：全持ち上げの長辺を制限し二辺の端点条件を使う。
規約：長辺の証拠を選び直さない。使われ方：元の三角形に沿う指定比較同型。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 概要：元の全持ち上げの長辺が元の二射の合成を表す。
方針：長辺の両端と底を同じ持ち上げから計算する。
規約：全持ち上げの射を直接使用。使われ方：存在だけからの同型の選び直しを除く。 -/
def TransportTrianglePrism.longWitness {E F G B K : SSet.{u + 1}}
    {p : E ⟶ B} {q : F ⟶ B} {r : G ⟶ B}
    [LeftFibration p] [LeftFibration q] [LeftFibration r]
    {R : LeftTransportRepresentation p} {S : LeftTransportRepresentation q}
    {T : LeftTransportRepresentation r}
    {a : K ⟶ leftUnstraighteningTransformationSpace R.diagram S.diagram}
    {b : K ⟶ leftUnstraighteningTransformationSpace S.diagram T.diagram}
    {c : K ⟶ leftUnstraighteningTransformationSpace R.diagram T.diagram}
    {f : E ⊗ K ⟶ F} {g : F ⊗ K ⟶ G}
    {w : TransportRepresentationFamilyWitness R S a f}
    {v : TransportRepresentationFamilyWitness S T b g}
    {H : (Δ[2] : SSet.{u + 1}) ⊗ (B ⊗ K) ⟶ SpaceInfinity.{u}}
    (L : TransportTrianglePrism w v H)
    (h₀₂ : (stdSimplex.δ (1 : Fin 3) ▷ (B ⊗ K)) ≫ H =
      coherentTransformationFamilyDiagram c) :
    TransportRepresentationFamilyWitness R T c (lift f (snd E K) ≫ g) := by
  let W := (stdSimplex.δ (1 : Fin 3) ▷ (E ⊗ K)) ≫ L.prism
  have hz : prismEndpoint 0 (E ⊗ K) ≫ (stdSimplex.δ (1 : Fin 3) ▷ (E ⊗ K)) =
      prismEndpoint 0 (E ⊗ K) ≫ (stdSimplex.δ (2 : Fin 3) ▷ (E ⊗ K)) := rfl
  have ho : prismEndpoint 1 (E ⊗ K) ≫ (stdSimplex.δ (1 : Fin 3) ▷ (E ⊗ K)) =
      prismEndpoint 1 (E ⊗ K) ≫ (stdSimplex.δ (0 : Fin 3) ▷ (E ⊗ K)) := rfl
  have hW₀ : prismEndpoint 0 (E ⊗ K) ≫ W = fst E K ≫ R.pointedMap := by
    dsimp only [W]
    rw [← Category.assoc, hz, Category.assoc, L.first,
      TransportRepresentationFamilyWitness.leftPrism, ← Category.assoc,
      prismEndpoint_associator_inv, w.source]
  have hv₁ : prismEndpoint 1 (F ⊗ K) ≫ v.leftPrism = g ≫ T.pointedMap := by
    rw [TransportRepresentationFamilyWitness.leftPrism, ← Category.assoc,
      prismEndpoint_associator_inv, v.target]
  have hW₁ : prismEndpoint 1 (E ⊗ K) ≫ W =
      (lift f (snd E K) ≫ g) ≫ T.pointedMap := by
    dsimp only [W]
    rw [← Category.assoc, ho, Category.assoc, L.second, ← Category.assoc,
      prismEndpoint_naturality, Category.assoc, hv₁, ← Category.assoc]
  have hWp : W ≫ pointedSpaceProjection =
      (Δ[1] ◁ (p ▷ K)) ≫ coherentTransformationFamilyDiagram c := by
    dsimp only [W]
    rw [Category.assoc, L.projection, trianglePrism_restrict_baseChange, h₀₂]
  refine {
    prism := (α_ Δ[1] E K).hom ≫ W
    source := ?_
    target := ?_
    projection := ?_ }
  · have he : (prismEndpoint 0 E ▷ K) ≫ (α_ (Δ[1] : SSet.{u + 1}) E K).hom =
        prismEndpoint 0 (E ⊗ K) := rfl
    rw [← Category.assoc, he, hW₀]
  · have he : (prismEndpoint 1 E ▷ K) ≫ (α_ (Δ[1] : SSet.{u + 1}) E K).hom =
        prismEndpoint 1 (E ⊗ K) := rfl
    rw [← Category.assoc, he, hW₁]
  · rw [Category.assoc, hWp, coherentTransformationFamilyDiagram]
    have he : (α_ (Δ[1] : SSet.{u + 1}) E K).hom ≫ (Δ[1] ◁ (p ▷ K)) =
        ((Δ[1] ◁ p) ▷ K) ≫ (α_ Δ[1] B K).hom := rfl
    rw [← Category.assoc, he]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]

end SerrePositivity.InfinityCategories.F2
