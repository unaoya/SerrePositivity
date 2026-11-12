module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentTotalMapNativeAction
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.CoherentTotalCoconeValuePre

/-!
概要：native 余極限写像の元の fiber 輸送と具体的 Kan 頂点射の指定比較。
方針：元の全空間余錐との合成作用を比較し、fiber 写像の前合成同値で反映する。
規約：選択済み native 射を保持。使われ方：引き戻し錐の二射影との照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
attribute [local instance] vertexFiber_kanComplex_of_leftFibration
variable {B C : SSet.{u}}
  (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
  (G : (SSet.uliftFunctor.{u + 1, u}).obj C ⟶ SpaceInfinity.{u})
  (a : smallLeftUnstraightening F ⟶ smallLeftUnstraightening G)

/-- 概要：元の native 余極限写像の実際の fiber 間輸送。
方針：元の輸送族を選択済み native な射で評価。
規約：指定輸送を変更しない。使われ方：具体的な Kan 射への比較。 -/
def coherentTotalMapNativeFiberTransport :
    vertexFiber pointedSpaceProjection (coherentDiagramTotalCocone F).vertex ⟶
      vertexFiber pointedSpaceProjection (coherentDiagramTotalVertex G) :=
  (functorVertexEquiv _ _).symm
    ((pointedIntervalTransport (pinchedHomLeftToIntervalMappingSpace
      (coherentDiagramTotalCocone F).vertex (coherentDiagramTotalVertex G))).map.app
        (Opposite.op ⦋0⦌) (coherentTotalMapNativeRepresentation F G a).1)

/-- 概要：native 射の全空間作用は元の余錐と実際の fiber 輸送の合成。
方針：前後合成の頂点の式と内部 Hom の頂点の往復。
規約：射の厳密な等式。使われ方：前合成同値による反映の入力。 -/
lemma coherentTotalMapNativeAction_eq :
    coherentTotalMapNativeAction F G a = coconeFiberMap (coherentDiagramTotalCocone F) ≫
      coherentTotalMapNativeFiberTransport F G a ≫
        (pointedSpaceFiberValueEquivalence (coherentDiagramTotalVertex G)).hom := by
  have ht : functorVertex (coherentTotalMapNativeFiberTransport F G a) =
      (pointedIntervalTransport (pinchedHomLeftToIntervalMappingSpace
        (coherentDiagramTotalCocone F).vertex (coherentDiagramTotalVertex G))).map.app
          (Opposite.op ⦋0⦌) (coherentTotalMapNativeRepresentation F G a).1 :=
    (functorVertexEquiv _ _).apply_symm_apply _
  have ht' := congrArg (fun v =>
    ((ihom (leftUnstraightening F)).map
      (pointedSpaceFiberValueEquivalence (coherentDiagramTotalVertex G)).hom).app
        (Opposite.op ⦋0⦌)
        (((pre (coconeFiberMap (coherentDiagramTotalCocone F))).app
          (vertexFiber pointedSpaceProjection (coherentDiagramTotalVertex G))).app
            (Opposite.op ⦋0⦌) v)) ht
  apply (functorVertexEquiv _ _).injective
  exact ((functorVertexEquiv _ _).apply_symm_apply _).trans ht'.symm

/-- 概要：元の native 射の fiber 輸送は値の比較を介して具体的 Kan 頂点射に整合。
方針：指定作用同型を元の単位比較へ続け、元の fiber 写像の充満忠実な前合成で反映。
規約：選択済みの native 射の実際の輸送。使われ方：元の二射影との指定比較。 -/
def coherentTotalMapNativeFiberTransportIso :
    FunctorIso (coherentTotalMapNativeFiberTransport F G a ≫
      (pointedSpaceFiberValueEquivalence (coherentDiagramTotalVertex G)).hom)
      (coherentTotalSourceValueMap F ≫
        (SSet.uliftFunctor.{u + 1, u}).map (coherentTotalVertexMap F G a)) := by
  have e := coherentTotalMapNativeActionIso F G a
  rw [coherentTotalMapNativeAction_eq] at e
  have e' := (coherentLargeTotalCoconeUnitIso F).postcomp
    ((SSet.uliftFunctor.{u + 1, u}).map (coherentTotalVertexMap F G a))
  have hp := (coherentTotalCoconeFiber_value_pre_homotopyEquivalence F
    (spaceInfinityObject (coherentDiagramTotalVertex G)).obj).isQCatEquivalence
  exact hp.isFullyFaithful.preimageVertexIso (e ≪≫ e'.symm)

end SerrePositivity.InfinityCategories.F2
