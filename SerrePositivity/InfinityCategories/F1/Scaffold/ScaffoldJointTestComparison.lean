module

public import SerrePositivity.InfinityCategories.F1.Scaffold.ScaffoldTestComparison
public import SerrePositivity.InfinityCategories.F1.Simplicial.SimplicialOverTestComparison

/-!
概要：strict transport の自然な復元 span を二変数の共同テスト同型へ実現する。
方針：両脚の全 Hom の自然性と前合成同値性を同じ共同実現に適用する。
規約：始域も標的も固定せず、各対象で逆を独立に選ばない。
使われ方：復元 span の逆を全空間側の coherent な比較へ接続するための入力。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories

/-- universal scaffold の前合成同値を、全始域・全標的の共同同型へ実現する。 -/
def universalScaffoldJointTestIso (C : Type u) [Category.{u} C] :
    FunctorIso
      (simplicialOverJointTest (leftFibrationOverEnriched (nerve C)))
      (simplicialOverJointTest (strictTransportReplacementOverEnriched C)) :=
  (universalScaffoldOverComparison C).jointTestIso
    (universalScaffoldOverComparison_isPrecompositionEquivalence C)

/-- taut scaffold も同じ二変数の共同族の同型を与える。 -/
def tautScaffoldJointTestIso (C : Type u) [Category.{u} C] :
    FunctorIso
      (simplicialOverJointTest (strictTransportWeightedOverEnriched C))
      (simplicialOverJointTest (strictTransportReplacementOverEnriched C)) :=
  (tautScaffoldOverComparison C).jointTestIso
    (tautScaffoldOverComparison_isPrecompositionEquivalence C)

/-- 元と復元後からの相対 Hom を、始域・標的・全高次で同時に比較する。 -/
def leftStrictTransportReconstructionJointTestIso (C : Type u) [Category.{u} C] :
    FunctorIso
      (simplicialOverJointTest (leftFibrationOverEnriched (nerve C)))
      (simplicialOverJointTest (strictTransportWeightedOverEnriched C)) :=
  universalScaffoldJointTestIso C ≪≫ (tautScaffoldJointTestIso C).symm

end SerrePositivity.InfinityCategories
