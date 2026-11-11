module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.RepresentationMappingSpaceMap
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftUnstraighteningCompositionLift
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.TransformationFamilyTriangle

/-!
概要：一般の表現間の二つの相対射の族を coherent な三角形に沿って合成する。
方針：pointed な二辺の prism を貼り、内ホーンを充填して長辺を取る。
規約：底もパラメーターも任意。三角形は族全体の入力として保持する。
使われ方：straightening の写像空間比較の合成との整合性。

対応節は Kerodon 5.1（Tag 01T1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations

/-- 概要：指定された coherent な三角形の長辺は相対射の族の合成を実現する。
方針：後半の prism を最初の射の族で引き戻して二辺を充填する。
規約：同じパラメーターを二つの射の評価で共有する。
使われ方：選択した比較射の合成則を族の一意性へ帰着する。 -/
lemma transportRepresentationCompositionFamilyWitness_nonempty
    {E F G B K : SSet.{u + 1}} {p : E ⟶ B} {q : F ⟶ B} {r : G ⟶ B}
    [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration q] [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration r]
    (R : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.LeftTransportRepresentation p) (S : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.LeftTransportRepresentation q)
    (T : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.LeftTransportRepresentation r)
    {t₀₁ : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningTransformationSpace R.diagram S.diagram}
    {t₁₂ : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningTransformationSpace S.diagram T.diagram}
    {t₀₂ : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningTransformationSpace R.diagram T.diagram}
    {f : E ⊗ K ⟶ F} {g : F ⊗ K ⟶ G}
    (hf : f ≫ q = fst E K ≫ p)
    (w : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.TransportRepresentationFamilyWitness R S t₀₁ f)
    (v : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.TransportRepresentationFamilyWitness S T t₁₂ g)
    (H : (Δ[2] : SSet.{u + 1}) ⊗ (B ⊗ K) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})
    (h₀₁ : (stdSimplex.δ (2 : Fin 3) ▷ (B ⊗ K)) ≫ H =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentTransformationFamilyDiagram t₀₁)
    (h₁₂ : (stdSimplex.δ (0 : Fin 3) ▷ (B ⊗ K)) ≫ H =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentTransformationFamilyDiagram t₁₂)
    (h₀₂ : (stdSimplex.δ (1 : Fin 3) ▷ (B ⊗ K)) ≫ H =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentTransformationFamilyDiagram t₀₂) :
    Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.TransportRepresentationFamilyWitness R T t₀₂ (lift f (snd E K) ≫ g)) := by
  let a : E ⊗ K ⟶ F ⊗ K := lift f (snd E K)
  have ha : a ≫ (q ▷ K) = p ▷ K := by
    apply CartesianMonoidalCategory.hom_ext
    · rw [Category.assoc, whiskerRight_fst, ← Category.assoc, lift_fst, hf,
        whiskerRight_fst]
    · rw [Category.assoc, whiskerRight_snd, lift_snd, whiskerRight_snd]
  have hv₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 (F ⊗ K) ≫ v.leftPrism = fst F K ≫ S.pointedMap := by
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.TransportRepresentationFamilyWitness.leftPrism, ← Category.assoc,
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.prismEndpoint_associator_inv, v.source]
  have hv₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (F ⊗ K) ≫ v.leftPrism = g ≫ T.pointedMap := by
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.TransportRepresentationFamilyWitness.leftPrism, ← Category.assoc,
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.prismEndpoint_associator_inv, v.target]
  let V := (Δ[1] ◁ a) ≫ v.leftPrism
  let b := (Δ[2] ◁ (p ▷ K)) ≫ H
  have hw : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (E ⊗ K) ≫ w.leftPrism =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 (E ⊗ K) ≫ V := by
    dsimp only [V]
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint_naturality, Category.assoc]
    rw [hv₀]
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.TransportRepresentationFamilyWitness.leftPrism, ← Category.assoc,
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.prismEndpoint_associator_inv, w.target]
    rw [← Category.assoc, lift_fst]
  have hw₀₁ : w.leftPrism ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection =
      (stdSimplex.δ (2 : Fin 3) ▷ (E ⊗ K)) ≫ b := by
    rw [w.leftPrism_projection, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.trianglePrism_restrict_baseChange, h₀₁]
  have hw₁₂ : V ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection =
      (stdSimplex.δ (0 : Fin 3) ▷ (E ⊗ K)) ≫ b := by
    dsimp only [V]
    rw [Category.assoc, v.leftPrism_projection, ← Category.assoc,
      ← MonoidalCategory.whiskerLeft_comp, ha, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.trianglePrism_restrict_baseChange, h₁₂]
  obtain ⟨L, hL₀₁, hL₁₂, hLp⟩ :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.innerFibration_fillTrianglePrism _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection w.leftPrism V b hw hw₀₁ hw₁₂
  let W := (stdSimplex.δ (1 : Fin 3) ▷ (E ⊗ K)) ≫ L
  have hz : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 (E ⊗ K) ≫ (stdSimplex.δ (1 : Fin 3) ▷ (E ⊗ K)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 (E ⊗ K) ≫ (stdSimplex.δ (2 : Fin 3) ▷ (E ⊗ K)) := rfl
  have ho : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (E ⊗ K) ≫ (stdSimplex.δ (1 : Fin 3) ▷ (E ⊗ K)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (E ⊗ K) ≫ (stdSimplex.δ (0 : Fin 3) ▷ (E ⊗ K)) := rfl
  have hW₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 (E ⊗ K) ≫ W = fst E K ≫ R.pointedMap := by
    dsimp only [W]
    rw [← Category.assoc, hz, Category.assoc, hL₀₁,
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.TransportRepresentationFamilyWitness.leftPrism, ← Category.assoc,
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.prismEndpoint_associator_inv, w.source]
  have hW₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (E ⊗ K) ≫ W = (a ≫ g) ≫ T.pointedMap := by
    dsimp only [W]
    rw [← Category.assoc, ho, Category.assoc, hL₁₂]
    dsimp only [V]
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint_naturality, Category.assoc, hv₁,
      ← Category.assoc]
  have hWp : W ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection =
      (Δ[1] ◁ (p ▷ K)) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentTransformationFamilyDiagram t₀₂ := by
    dsimp only [W]
    rw [Category.assoc, hLp, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.trianglePrism_restrict_baseChange, h₀₂]
  refine ⟨{
    prism := (α_ Δ[1] E K).hom ≫ W
    source := ?_
    target := ?_
    projection := ?_ }⟩
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

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
