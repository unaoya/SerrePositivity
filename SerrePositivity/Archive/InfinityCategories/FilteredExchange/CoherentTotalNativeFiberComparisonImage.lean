module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentTotalMapNativeTransport
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.FullyFaithfulFunctorIsoCoherence
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.FunctorIsoWhiskerAlgebra
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.VertexIsoCompositionTransport

/-!
概要：元の native 輸送と具体的 Kan 射の比較を、元の余錐 fiber 写像で回収する。
方針：構成した同じ充満忠実な逆像の像を計算し、端点表示の輸送だけを除く。
規約：native 表現と二指定比較を保持。使われ方：raw 輸送模型比較の元の単位での像。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.F2
attribute [local instance] vertexFiber_kanComplex_of_leftFibration
variable {B C : SSet.{u}}
  (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
  (G : (SSet.uliftFunctor.{u + 1, u}).obj C ⟶ SpaceInfinity.{u})
  (a : smallLeftUnstraightening F ⟶ smallLeftUnstraightening G)
local notation "c" => coconeFiberMap (coherentDiagramTotalCocone F)
local notation "m" => CategoryTheory.Functor.map SSet.uliftFunctor (coherentTotalVertexMap F G a)

/-- 同じ native 輸送模型比較の単位での像は、元の作用比較と同じ余錐単位比較の逆。 -/
lemma coherentTotalMapNativeFiberTransportIso_precomp_heq :
    HEq ((coherentTotalMapNativeFiberTransportIso F G a).precomp c)
      (coherentTotalMapNativeActionIso F G a ≪≫
        ((coherentLargeTotalCoconeUnitIso F).postcomp m).symm) := by
  unfold coherentTotalMapNativeFiberTransportIso
  rw [functorIso_precomp_eq_mapIso]
  change HEq (VertexIso.map _ _) _
  rw [IsFullyFaithful.preimageVertexIso_map]
  refine vertexIso_trans_heq_of_heq _ _ _ _
    (congrArg functorVertex (coherentTotalMapNativeAction_eq F G a)).symm rfl rfl ?_ HEq.rfl
  exact cast_heq (congrArg (fun r => FunctorIso r (coherentLargeTotalUnit F ≫ m))
    (coherentTotalMapNativeAction_eq F G a)) (coherentTotalMapNativeActionIso F G a)

end SerrePositivity.InfinityCategories.F2
