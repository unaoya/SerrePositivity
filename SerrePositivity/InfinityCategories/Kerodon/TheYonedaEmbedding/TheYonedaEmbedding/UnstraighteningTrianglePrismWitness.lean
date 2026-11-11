module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.TransportTrianglePrismWitness
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.UnstraighteningFamilyWitnessRestriction

/-!
概要：標準 unstraightening の二辺の全三角形から長辺の証拠を直接得る。
方針：同じ保持した prism を標準表現の座標へ戻す。
規約：証拠の存在から再選択しない。使われ方：指定された合成比較同型。

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

/-- 概要：保持した元の全三角形の長辺を標準 unstraightening の証拠にする。
方針：標準表現の比較が恒等であることを使い端点表示だけを揃える。
規約：元の長辺 prism を保持。使われ方：存在だけからの同型の再選択を除く。 -/
def unstraighteningFamilyTriangleWitnessOfPrism {B K : SSet.{u + 1}}
    (F G J : B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})
    {a : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningTransformationSpace F G}
    {b : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningTransformationSpace G J}
    {c : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningTransformationSpace F J}
    {f : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraightening F ⊗ K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraightening G}
    {g : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraightening G ⊗ K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraightening J}
    (w : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.UnstraighteningFamilyWitness F G a f)
    (v : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.UnstraighteningFamilyWitness G J b g)
    (H : (Δ[2] : SSet.{u + 1}) ⊗ (B ⊗ K) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})
    (L : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.TransportTrianglePrism w.toRepresentationWitness v.toRepresentationWitness H)
    (h₀₂ : (stdSimplex.δ (1 : Fin 3) ▷ (B ⊗ K)) ≫ H =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentTransformationFamilyDiagram c) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.UnstraighteningFamilyWitness F J c
      (lift f (snd (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraightening F) K) ≫ g) := by
  let W := L.longWitness h₀₂
  refine ⟨W.prism, ?_, ?_, W.projection⟩
  · simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.unstraighteningTransportRepresentation, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.LeftTransportRepresentation.pointedMap,
      Category.id_comp] using W.source
  · simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.unstraighteningTransportRepresentation, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.LeftTransportRepresentation.pointedMap,
      Category.id_comp] using W.target

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding
