module

public import SerrePositivity.InfinityCategories.F2.CoherentTotalMapNativeAction
public import SerrePositivity.InfinityCategories.F2.VertexIsoEndpointTransport
public import SerrePositivity.InfinityCategories.F2.VertexIsoCompositionTransport

/-!
概要：元の native 作用比較を、同じ全 Hom 比較の成分と同じ指定余錐比較へ戻す。
方針：実射の頂点表示による等式移送だけを除く。
規約：native な射と比較を選び直さない。使われ方：上側 native 因子への全 Hom 自然性の移送。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {B C : SSet.{u}}
  (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
  (G : (SSet.uliftFunctor.{u + 1, u}).obj C ⟶ SpaceInfinity.{u})
  (a : smallLeftUnstraightening F ⟶ smallLeftUnstraightening G)

/-- 元の native 作用比較は、元の全 Hom 比較の成分の逆と指定余錐比較の像の合成。 -/
lemma coherentTotalMapNativeActionIso_heq_components :
    HEq (coherentTotalMapNativeActionIso F G a)
      (((coherentCoconeTransportActionIso F (coherentDiagramTotalCocone F)
        (coherentDiagramTotalVertex G)).app
          (coherentTotalMapNativeRepresentation F G a).1).symm ≪≫
        vertexIsoOfEq (VertexIso.map (coherentTotalMapNativeComparisonIso F G a)
          (smallUnstraighteningHomIso F
            (spaceInfinityObject (coherentDiagramTotalVertex G)).obj).inv) rfl
          (smallUnstraighteningHomIso_inv_vertex F
            (coherentDiagramTotalUnit F ≫ coherentTotalVertexMap F G a))) := by
  unfold coherentTotalMapNativeActionIso
  exact vertexIsoOfEq_heq _ _ _

/-- 元の native 作用比較の逆も、同じ二つの指定成分の合成の逆に一致する。 -/
lemma coherentTotalMapNativeActionIso_symm_heq_components :
    HEq (coherentTotalMapNativeActionIso F G a).symm
      (coherentTotalMapNativeActionComponentsIso F G a).symm := by
  have hs : functorVertex (coherentTotalMapNativeAction F G a) =
      (coherentCoconeTransportAction F (coherentDiagramTotalCocone F)
        (coherentDiagramTotalVertex G)).app (Opposite.op ⦋0⦌)
          (coherentTotalMapNativeRepresentation F G a).1 :=
    (functorVertexEquiv _ _).apply_symm_apply _
  exact vertexIso_symm_heq_of_heq (coherentTotalMapNativeActionIso F G a)
    (coherentTotalMapNativeActionComponentsIso F G a) hs
    (congrArg functorVertex (coherentTotalMapNativeActionComponents_target F G a).symm)
    (coherentTotalMapNativeActionIso_heq_components F G a)

end SerrePositivity.InfinityCategories.F2
