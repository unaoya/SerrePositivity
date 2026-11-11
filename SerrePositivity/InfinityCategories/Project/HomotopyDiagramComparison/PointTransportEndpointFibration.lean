module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.FixedExtensionPointEndpoint
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.EdgeEndpointPairMono
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.PointTransportExtension
public import
  SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SpecifiedCoconeRightCorrectionEndpoint

/-!
概要：元の根辺の固定初期値の終点評価は left fibration であることを無条件に示す。
方針：二端点の結合した包含の単射性を、同じ相対終点評価の定理へ代入する。
規約：終点評価を新しい射へ置き換えない。使われ方：根辺の終点辺の厳密な定値化。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
noncomputable section

/-- 同じ点輸送の根辺延長の終点評価は left fibration。 -/
instance pointTransportExtensionEndpoint_leftFibration {E B : SSet.{u}}
    (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] {a c : B _⦋0⦌} (g : B.Edge a c)
    (v : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p a) _⦋0⦌) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pointTransportExtensionEndpoint p g v) := by
  dsimp only [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pointTransportExtensionEndpoint]
  have : Mono (coprod.desc (stdSimplex.δ (1 : Fin 2) : (Δ[0] : SSet.{u}) ⟶ Δ[1])
      (stdSimplex.δ (0 : Fin 2) ≫ 𝟙 Δ[1])) := by
    simpa only [Category.comp_id] using _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.edgeEndpointPair_mono.{u}
  infer_instance

attribute [local irreducible] _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitStrictSpanCocone _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitApexSpan
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpanRootLeg _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpanLeftLeg _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpanRightLeg

/-- 元の指定余錐の共通根辺の同じ終点評価も left fibration。 -/
instance specifiedCoconeRightRootEndpoint_leftFibration
    {A B C D : SSet.{u + 1}} {f : A ⟶ B} {g : A ⟶ C}
    {i : B ⟶ D} {j : C ⟶ D} (hp : IsPushout f g i j) [Mono g]
    (p : D ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}) (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (f ≫ (i ≫ p))) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c)
    (dB : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (i ≫ p)) (dC : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (j ≫ p)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRightRootEndpoint hp p c hc dB dC) := by
  dsimp only [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRightRootEndpoint]
  have : Mono (coprod.desc (stdSimplex.δ (1 : Fin 2) : (Δ[0] : SSet.{u + 1}) ⟶ Δ[1])
      (stdSimplex.δ (0 : Fin 2) ≫ 𝟙 Δ[1])) := by
    simpa only [Category.comp_id] using _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.edgeEndpointPair_mono.{u + 1}
  infer_instance

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
