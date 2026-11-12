module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitFiberTransportRecovery
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.FullyFaithfulVertexIsoImage
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.FunctorIsoWhiskerAlgebra
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.FunctorIsoWhiskerVertexMap
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentCoconeIntervalTransportAction
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitUnitActionConjugacy

/-!
概要：a6 の元の指定 fiber 輸送比較を、構成時の同じ全空間比較の像へ戻す。
方針：同じ二段の充満忠実性による逆像の像を計算し、元の上下作用比較を保持する。
規約：指定比較を再選択しない。使われ方：完成済み比較の三角形整合の像での検証。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.F2
attribute [local instance] vertexFiber_kanComplex_of_leftFibration
variable (B : SSet.{u})
  {F G : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}} (H : SSet.Homotopy F G)
local notation "f" => coconeFiberMap (coherentDiagramTotalCocone F)
local notation "a" => coherentTransformationTotalMap F G (coherentVertexOfHomotopy H)
local notation "v" => QCatEquivalence.hom
  (pointedSpaceFiberValueEquivalence (coherentDiagramTotalVertex G))

/-- 元の指定 fiber 輸送比較の値への像は、元の指定された値の比較そのもの。 -/
lemma coherentColimitFiberTransportIso_postcomp_value :
    (coherentColimitFiberTransportIso B H).postcomp v =
      coherentColimitFiberTransportComparisonIso B H := by
  rw [functorIso_postcomp_eq_mapIso]
  unfold coherentColimitFiberTransportIso
  exact vertexIso_map_preimage _ _

/-- 元の指定比較の二段の像は、元の上下作用比較の同じ合成に値まで戻る。 -/
lemma coherentColimitFiberTransportIso_value_precomp_heq_actions :
    HEq (((coherentColimitFiberTransportIso B H).postcomp v).precomp f)
      ((coherentColimitLowerActionIso B H).symm ≪≫ coherentColimitUpperActionIso B H) := by
  rw [coherentColimitFiberTransportIso_postcomp_value]
  exact coherentColimitFiberTransportComparisonIso_precomp_heq B H

/-- 元の上下作用比較と同じ二段の像を持つ比較は、元の指定 fiber 比較と値まで一致する。 -/
lemma coherentColimitFiberTransportIso_unique
    (n : FunctorIso (coherentColimitFiberTransport B H)
      (coherentTotalMapNativeFiberTransport F G a))
    (hn : HEq ((n.postcomp v).precomp f)
      ((coherentColimitLowerActionIso B H).symm ≪≫ coherentColimitUpperActionIso B H)) :
    n = coherentColimitFiberTransportIso B H := by
  have he : (n.postcomp v).precomp f =
      ((coherentColimitFiberTransportIso B H).postcomp v).precomp f :=
    eq_of_heq (hn.trans (coherentColimitFiberTransportIso_value_precomp_heq_actions B H).symm)
  have hp := (coherentTotalCoconeFiber_value_pre_homotopyEquivalence F
    (spaceInfinityObject (coherentDiagramTotalVertex G)).obj).isQCatEquivalence
  have hv := (pointedSpaceFiberValueEquivalence (coherentDiagramTotalVertex G)).isQCatEquivalence
    |>.postcompose (vertexFiber pointedSpaceProjection (coherentDiagramTotalCocone F).vertex)
  have he' : n.postcomp v = (coherentColimitFiberTransportIso B H).postcomp v := by
    apply Iso.ext
    apply hp.isFullyFaithful.toHoFullyFaithful.map_injective
    simpa only [functorIso_precomp_eq_mapIso, Functor.mapIso_hom, hoFunctor_map,
      Functor.toCatHom_toFunctor] using congrArg Iso.hom he
  apply Iso.ext
  apply hv.isFullyFaithful.toHoFullyFaithful.map_injective
  simpa only [functorIso_postcomp_eq_mapIso, Functor.mapIso_hom, hoFunctor_map,
    Functor.toCatHom_toFunctor] using congrArg Iso.hom he'

/-- 元の指定 fiber 比較の共通の全作用の像は、同じ元の上下作用比較に値まで戻る。 -/
lemma coherentColimitFiberTransportIso_action_heq :
    HEq (VertexIso.map (coherentColimitFiberTransportIso B H)
      (coherentCoconeFiberValueAction F (coherentDiagramTotalCocone F)
        (coherentDiagramTotalVertex G)))
      ((coherentColimitLowerActionIso B H).symm ≪≫ coherentColimitUpperActionIso B H) := by
  exact (functorIso_whisker_vertexMap_heq (coherentColimitFiberTransportIso B H) f v).trans
    (coherentColimitFiberTransportIso_value_precomp_heq_actions B H)

/-- 元の指定比較の共通の全作用の像は、同じ三角形比較の指定共役に一致する。 -/
lemma coherentColimitFiberTransportIso_action_heq_conjugate :
    HEq (VertexIso.map (coherentColimitFiberTransportIso B H)
      (coherentCoconeFiberValueAction F (coherentDiagramTotalCocone F)
        (coherentDiagramTotalVertex G)))
      ((coherentColimitLowerTransportFactorIso B H).symm ≪≫
        coherentColimitNativeTriangleActionComparison B H ≪≫
          coherentColimitUpperTransportFactorIso B H) := by
  exact (coherentColimitFiberTransportIso_action_heq B H).trans
    (heq_of_eq (coherentColimitActionComparison_eq_conjugate B H))

end SerrePositivity.InfinityCategories.F2
