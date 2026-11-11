module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentCoconeIntervalTransportAction
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentTotalMapNativeActionComponents
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.FunctorIsoTriangleEvaluation

/-!
概要：全 Hom の普遍作用比較の成分を、元の native 作用の指定成分へ戻す。
方針：同じ全関手同型の二段の合成を各点で評価する。
規約：元の成分と指定余錐比較を保持。使われ方：上側 native 因子の普遍輸送との照合。
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
local notation "z" => coherentDiagramTotalVertex G
local notation "n" => Sigma.fst (coherentTotalMapNativeRepresentation F G a)
local notation "S" => Iso.inv (smallUnstraighteningHomIso F (KanObject.obj (spaceInfinityObject z)))
local notation "u₀" => vertexIsoOfEq (VertexIso.map (coherentTotalMapNativeComparisonIso F G a) S)
  rfl (smallUnstraighteningHomIso_inv_vertex F
    (coherentDiagramTotalUnit F ≫ coherentTotalVertexMap F G a))

/-- 普遍作用による元の二成分は、普遍輸送成分の逆と既存 native 成分の同じ合成。 -/
lemma coherentTotalMapNativeIntervalComponents_eq_original :
    ((coherentCoconeIntervalTransportActionIso F (coherentDiagramTotalCocone F) z).app n).symm ≪≫
      u₀ =
    ((coherentCoconeUniversalTransportIso F (coherentDiagramTotalCocone F) z).app n).symm ≪≫
      coherentTotalMapNativeActionComponentsIso F G a := by
  unfold coherentCoconeIntervalTransportActionIso coherentTotalMapNativeActionComponentsIso
  rw [FunctorIso.app_trans, Iso.trans_symm, Iso.trans_assoc]

/-- 元の普遍輸送成分を戻すと、既存 native 成分そのものを回収する。 -/
lemma coherentTotalMapNativeIntervalComponents_cancel :
    (coherentCoconeUniversalTransportIso F (coherentDiagramTotalCocone F) z).app n ≪≫
      (((coherentCoconeIntervalTransportActionIso F (coherentDiagramTotalCocone F) z).app n).symm ≪≫
        u₀) = coherentTotalMapNativeActionComponentsIso F G a := by
  rw [coherentTotalMapNativeIntervalComponents_eq_original]
  simp only [← Iso.trans_assoc, Iso.self_symm_id, Iso.refl_trans]

end SerrePositivity.InfinityCategories.F2
