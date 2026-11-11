module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.TransportTrianglePrismChoice

/-!
概要：保持した元の全三角形の長辺から合成の pointed な証拠を取り出す。
方針：全持ち上げの長辺を制限し二辺の端点条件を使う。
規約：長辺の証拠を選び直さない。使われ方：元の三角形に沿う指定比較同型。

対応節は Kerodon 8.3（Tag 03LZ）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding

/-- 概要：元の全持ち上げの長辺が元の二射の合成を表す。
方針：長辺の両端と底を同じ持ち上げから計算する。
規約：全持ち上げの射を直接使用。使われ方：存在だけからの同型の選び直しを除く。 -/
def TransportTrianglePrism.longWitness {E F G B K : SSet.{u + 1}}
    {p : E ⟶ B} {q : F ⟶ B} {r : G ⟶ B}
    [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration q] [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration r]
    {R : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.LeftTransportRepresentation p} {S : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.LeftTransportRepresentation q}
    {T : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.LeftTransportRepresentation r}
    {a : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningTransformationSpace R.diagram S.diagram}
    {b : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningTransformationSpace S.diagram T.diagram}
    {c : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningTransformationSpace R.diagram T.diagram}
    {f : E ⊗ K ⟶ F} {g : F ⊗ K ⟶ G}
    {w : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.TransportRepresentationFamilyWitness R S a f}
    {v : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.TransportRepresentationFamilyWitness S T b g}
    {H : (Δ[2] : SSet.{u + 1}) ⊗ (B ⊗ K) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}}
    (L : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.TransportTrianglePrism w v H)
    (h₀₂ : (stdSimplex.δ (1 : Fin 3) ▷ (B ⊗ K)) ≫ H =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentTransformationFamilyDiagram c) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.TransportRepresentationFamilyWitness R T c (lift f (snd E K) ≫ g) := by
  let W := (stdSimplex.δ (1 : Fin 3) ▷ (E ⊗ K)) ≫ L.prism
  have hz : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 (E ⊗ K) ≫ (stdSimplex.δ (1 : Fin 3) ▷ (E ⊗ K)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 (E ⊗ K) ≫ (stdSimplex.δ (2 : Fin 3) ▷ (E ⊗ K)) := rfl
  have ho : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (E ⊗ K) ≫ (stdSimplex.δ (1 : Fin 3) ▷ (E ⊗ K)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (E ⊗ K) ≫ (stdSimplex.δ (0 : Fin 3) ▷ (E ⊗ K)) := rfl
  have hW₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 (E ⊗ K) ≫ W = fst E K ≫ R.pointedMap := by
    dsimp only [W]
    rw [← Category.assoc, hz, Category.assoc, L.first,
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.TransportRepresentationFamilyWitness.leftPrism, ← Category.assoc,
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.prismEndpoint_associator_inv, w.source]
  have hv₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (F ⊗ K) ≫ v.leftPrism = g ≫ T.pointedMap := by
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.TransportRepresentationFamilyWitness.leftPrism, ← Category.assoc,
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.prismEndpoint_associator_inv, v.target]
  have hW₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (E ⊗ K) ≫ W =
      (lift f (snd E K) ≫ g) ≫ T.pointedMap := by
    dsimp only [W]
    rw [← Category.assoc, ho, Category.assoc, L.second, ← Category.assoc,
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint_naturality, Category.assoc, hv₁, ← Category.assoc]
  have hWp : W ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection =
      (Δ[1] ◁ (p ▷ K)) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentTransformationFamilyDiagram c := by
    dsimp only [W]
    rw [Category.assoc, L.projection, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.trianglePrism_restrict_baseChange, h₀₂]
  refine {
    prism := (α_ Δ[1] E K).hom ≫ W
    source := ?_
    target := ?_
    projection := ?_ }
  · have he : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 E ▷ K) ≫ (α_ (Δ[1] : SSet.{u + 1}) E K).hom =
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 (E ⊗ K) := rfl
    rw [← Category.assoc, he, hW₀]
  · have he : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 E ▷ K) ≫ (α_ (Δ[1] : SSet.{u + 1}) E K).hom =
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (E ⊗ K) := rfl
    rw [← Category.assoc, he, hW₁]
  · rw [Category.assoc, hWp, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentTransformationFamilyDiagram]
    have he : (α_ (Δ[1] : SSet.{u + 1}) E K).hom ≫ (Δ[1] ◁ (p ▷ K)) =
        ((Δ[1] ◁ p) ▷ K) ≫ (α_ Δ[1] B K).hom := rfl
    rw [← Category.assoc, he]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding
