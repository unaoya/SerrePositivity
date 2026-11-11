module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.RepresentationFamilyWitness
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.SmallCoherentFamilyUniqueness

/-!
概要：一般の選択表現の間の相対射の族の実現の一意性。
方針：指定端点の collage による比較を族全体の変換空間へ戻す。
規約：実現の構成から一意性の依存を分離する。
使われ方：straightening の写像空間の比較の選択独立性。

対応節は Kerodon 7.4（Tag 02SX）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces

/-- 概要：同じ相対射の族の二つの実現は変換の族全体で関手同型。
方針：積の底上の指定表現の coherent な実現の一意性へ戻す。
規約：次数 fiber の小ささを明示し底やパラメーターは任意。
使われ方：写像空間の比較の選択独立性。 -/
lemma TransportRepresentationFamilyWitness.unique {E F B K : SSet.{u + 1}}
    {p : E ⟶ B} {q : F ⟶ B} [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration q]
    {R : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.LeftTransportRepresentation p} {S : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.LeftTransportRepresentation q}
    (hp : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.HasSmallSimplexFibers p) (hq : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.HasSmallSimplexFibers q)
    {t t' : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningTransformationSpace R.diagram S.diagram} {f : E ⊗ K ⟶ F}
    (hf : f ≫ q = fst E K ≫ p)
    (w : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.TransportRepresentationFamilyWitness R S t f)
    (w' : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.TransportRepresentationFamilyWitness R S t' f) : Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso t t') := by
  have hs : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 (E ⊗ K) ≫ w.leftPrism = fst E K ≫ R.pointedMap := by
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.TransportRepresentationFamilyWitness.leftPrism, ← Category.assoc,
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.prismEndpoint_associator_inv]
    exact w.source
  have ht : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (E ⊗ K) ≫ w.leftPrism = f ≫ S.pointedMap := by
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.TransportRepresentationFamilyWitness.leftPrism, ← Category.assoc,
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.prismEndpoint_associator_inv]
    exact w.target
  have hs' : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 (E ⊗ K) ≫ w'.leftPrism = fst E K ≫ R.pointedMap := by
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.TransportRepresentationFamilyWitness.leftPrism, ← Category.assoc,
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.prismEndpoint_associator_inv]
    exact w'.source
  have ht' : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (E ⊗ K) ≫ w'.leftPrism = f ≫ S.pointedMap := by
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.TransportRepresentationFamilyWitness.leftPrism, ← Category.assoc,
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.prismEndpoint_associator_inv]
    exact w'.target
  obtain ⟨e⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentFamily_uniqueness_of_small_fibers p q f hf hp hq R S
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentTransformationFamilyDiagram t) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentTransformationFamilyDiagram t')
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentTransformationFamilyDiagram_zero t) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentTransformationFamilyDiagram_one t)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentTransformationFamilyDiagram_zero t') (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentTransformationFamilyDiagram_one t')
    w.leftPrism w'.leftPrism hs ht hs' ht' w.leftPrism_projection w'.leftPrism_projection
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentTransformationFamilyDiagram_curry, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentTransformationFamilyDiagram_curry] at e
  exact ⟨e⟩

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces
