module

public import SerrePositivity.InfinityCategories.F2.CoherentColimitIntervalNativeSquare
public import SerrePositivity.InfinityCategories.F2.CoherentCoconeIntervalActionReflection
public import SerrePositivity.InfinityCategories.F2.VertexIsoTriangleRelationMap
public import SerrePositivity.InfinityCategories.F2.CoherentColimitIntervalNativeActionComponent

/-!
概要：a6 の選択済み区間比較の指定正方形を、全 Hom と共通の普遍作用へ移す。
方針：同じ元の正方形全体を、同じ余錐 fiber・値の作用で写す。
規約：元の二成分と選択済み比較を保持。使われ方：完成済み三角形の像の照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable (B : SSet.{u})
  {F G : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}} (H : SSet.Homotopy F G)
local notation "x" => JoinCocone.vertex (coherentDiagramTotalCocone F)
local notation "z" => coherentDiagramTotalVertex G
local notation "S" => coherentCoconeFiberValueAction F (coherentDiagramTotalCocone F) z
local notation "C" => coherentCoconeIntervalTransportAction F (coherentDiagramTotalCocone F) z

/-- 選択済み区間比較の同じ指定正方形は、全 Hom と共通の普遍作用でも可換。 -/
lemma coherentColimitIntervalNativeAction_square :
    VertexIso.map (coherentColimitIntervalCompletedTransportIso B H) S ≪≫
      VertexIso.map (coherentColimitIntervalNativeIso B H) C =
    VertexIso.map (coherentColimitFiberTransportIso B H) S ≪≫
      VertexIso.map (coherentColimitIntervalNativeTransportIso B H) S := by
  have h := congrArg (fun e => VertexIso.map e S) (coherentColimitIntervalNativeIso_square B H)
  simpa only [vertexIso_map_trans, vertexIso_map_comp,
    coherentCoconeIntervalTransportAction] using h

/-- a6 の元の正方形は、模型側と同じ全 Hom の普遍輸送成分を使っても厳密に可換。 -/
lemma coherentColimitIntervalNativeAction_universal_square :
    VertexIso.map (coherentColimitIntervalCompletedTransportIso B H) S ≪≫
      VertexIso.map (coherentColimitIntervalNativeIso B H) C =
    vertexIsoOfEq (VertexIso.map (coherentColimitFiberTransportIso B H) S) rfl
      (coherentColimitIntervalNativeActionSource_eq B H) ≪≫
        (coherentCoconeUniversalTransportIso F (coherentDiagramTotalCocone F) z).app
          (Sigma.fst (coherentTotalMapNativeRepresentation F G
            (coherentTransformationTotalMap F G (coherentVertexOfHomotopy H)))) := by
  exact vertexIso_square_of_heq _ _ _ _ _ _ _ _ rfl rfl
    (coherentColimitIntervalNativeActionSource_eq B H) rfl HEq.rfl HEq.rfl
    (vertexIsoOfEq_heq _ rfl (coherentColimitIntervalNativeActionSource_eq B H)).symm
    (coherentColimitIntervalNativeTransportIso_action_heq B H)
    (coherentColimitIntervalNativeAction_square B H)

/-- 共通の全作用で同じ元の正方形を満たす比較は、a6 の元の指定値と一致する。 -/
lemma coherentColimitIntervalNativeAction_unique
    (n : VertexIso (coherentColimitIntervalVertex B H)
      ((pinchedHomLeftToIntervalMappingSpace x z).app (Opposite.op ⦋0⦌)
        (Sigma.fst (coherentTotalMapNativeRepresentation F G
          (coherentTransformationTotalMap F G (coherentVertexOfHomotopy H))))))
    (hn : VertexIso.map (coherentColimitIntervalCompletedTransportIso B H) S ≪≫
      VertexIso.map n C = VertexIso.map (coherentColimitFiberTransportIso B H) S ≪≫
        VertexIso.map (coherentColimitIntervalNativeTransportIso B H) S) :
    n = coherentColimitIntervalNativeIso B H := by
  apply coherentCoconeIntervalTransportAction_iso_injective F z
  change VertexIso.map n C = VertexIso.map (coherentColimitIntervalNativeIso B H) C
  have h := hn.trans (coherentColimitIntervalNativeAction_square B H).symm
  have hh := congrArg (fun k =>
    (VertexIso.map (coherentColimitIntervalCompletedTransportIso B H) S).symm ≪≫ k) h
  simpa only [← Iso.trans_assoc, Iso.symm_self_id, Iso.refl_trans] using hh

end SerrePositivity.InfinityCategories.F2
