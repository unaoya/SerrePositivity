module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.TransportTrianglePrism

/-!
概要：指定された coherent 全三角形と元の二辺を保持する pointed な持ち上げを選ぶ。
方針：元の底の三角形上で内ホーン prism を充填する。
規約：選択の型に元の全二単体を含める。使われ方：指定された合成比較。

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

/-- 概要：二つの指定 prism を元の底の全三角形に沿って充填する。
方針：元の第二辺を第一射で引き戻して内ホーン充填を適用する。
規約：存在命題は全持ち上げ構造についてのみ使う。使われ方：元の二次整合の保持。 -/
def transportTrianglePrism {E F G B K : SSet.{u + 1}}
    {p : E ⟶ B} {q : F ⟶ B} {r : G ⟶ B}
    [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration q] [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration r]
    {R : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.LeftTransportRepresentation p} {S : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.LeftTransportRepresentation q}
    {T : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.LeftTransportRepresentation r}
    {a : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningTransformationSpace R.diagram S.diagram}
    {b : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningTransformationSpace S.diagram T.diagram}
    {f : E ⊗ K ⟶ F} {g : F ⊗ K ⟶ G}
    (hf : f ≫ q = fst E K ≫ p)
    (w : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.TransportRepresentationFamilyWitness R S a f)
    (v : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.TransportRepresentationFamilyWitness S T b g)
    (H : (Δ[2] : SSet.{u + 1}) ⊗ (B ⊗ K) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})
    (h₀₁ : (stdSimplex.δ (2 : Fin 3) ▷ (B ⊗ K)) ≫ H =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentTransformationFamilyDiagram a)
    (h₁₂ : (stdSimplex.δ (0 : Fin 3) ▷ (B ⊗ K)) ≫ H =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentTransformationFamilyDiagram b) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.TransportTrianglePrism w v H :=
  Classical.choice <| by
  let m : E ⊗ K ⟶ F ⊗ K := lift f (snd E K)
  have hm : m ≫ (q ▷ K) = p ▷ K := by
    apply CartesianMonoidalCategory.hom_ext
    · rw [Category.assoc, whiskerRight_fst, ← Category.assoc, lift_fst, hf, whiskerRight_fst]
    · rw [Category.assoc, whiskerRight_snd, lift_snd, whiskerRight_snd]
  have hv₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 (F ⊗ K) ≫ v.leftPrism = fst F K ≫ S.pointedMap := by
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.TransportRepresentationFamilyWitness.leftPrism, ← Category.assoc,
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.prismEndpoint_associator_inv, v.source]
  let V := (Δ[1] ◁ m) ≫ v.leftPrism
  let D := (Δ[2] ◁ (p ▷ K)) ≫ H
  have hw : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (E ⊗ K) ≫ w.leftPrism =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 (E ⊗ K) ≫ V := by
    dsimp only [V]
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint_naturality, Category.assoc, hv₀]
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.TransportRepresentationFamilyWitness.leftPrism, ← Category.assoc,
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.prismEndpoint_associator_inv, w.target, ← Category.assoc, lift_fst]
  have hfirst : w.leftPrism ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection =
      (stdSimplex.δ (2 : Fin 3) ▷ (E ⊗ K)) ≫ D := by
    rw [w.leftPrism_projection, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.trianglePrism_restrict_baseChange, h₀₁]
  have hsecond : V ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection =
      (stdSimplex.δ (0 : Fin 3) ▷ (E ⊗ K)) ≫ D := by
    dsimp only [V]
    rw [Category.assoc, v.leftPrism_projection, ← Category.assoc,
      ← MonoidalCategory.whiskerLeft_comp, hm, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.trianglePrism_restrict_baseChange, h₁₂]
  obtain ⟨L, hL₀₁, hL₁₂, hLp⟩ :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.innerFibration_fillTrianglePrism _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection w.leftPrism V D hw hfirst hsecond
  exact ⟨⟨L, hL₀₁, hL₁₂, hLp⟩⟩

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding
