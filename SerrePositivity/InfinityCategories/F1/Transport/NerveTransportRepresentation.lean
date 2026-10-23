module

public import SerrePositivity.InfinityCategories.F1.Transport.LeftTransportRepresentationRestriction
public import SerrePositivity.InfinityCategories.F1.Fibrations.LeftCoherentTransportDirectComparison
public import SerrePositivity.InfinityCategories.F1.Fibrations.LeftFibrationFiberReflection

/-!
概要：通常の圏の nerve 上の left fibration の実際の transport representation。
方針：構成済みの coherent transport の比較を用い、全空間の同値から各 fiber の同値を回収する。
規約：小さい全空間と底を一段持ち上げて空間の宇宙に合わせる。
使われ方：Kerodon §§5.6.2、5.6.5、標準単体上の相対表現の候補の供給。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories

/-- 概要：通常の nerve 上の任意の小さい left fibration は実際の空間値表現を持つ。
方針：coherent transport への直接比較と fiber の同値判定を束ねる。
規約：分類図式と全空間の比較射をともに明示する。
使われ方：Kerodon Corollary 5.6.0.6、相対延長の局所的な候補の出発点。 -/
noncomputable def nerveLeftTransportRepresentation
    {C : Type u} [Category.{u} C] {E : SSet.{u}}
    (p : E ⟶ nerve C) [LeftFibration p] :
    LeftTransportRepresentation ((SSet.uliftFunctor.{u + 1, u}).map p) where
  diagram := leftCoherentTransport p
  comparison := leftCoherentTransportDirectComparison p
  over_base := leftCoherentTransportDirectComparison_projection p
  fiber_equivalence b :=
    vertexFiberMap_isQCatEquivalence_of_precompositionEquivalence
      ((SSet.uliftFunctor.{u + 1, u}).map p)
      (leftUnstraighteningProjection (leftCoherentTransport p))
      (leftCoherentTransportDirectComparison p) (leftCoherentTransportDirectComparison_projection p)
      (leftCoherentTransportDirectComparison_isPrecompositionEquivalence p) b

end SerrePositivity.InfinityCategories
