module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentNativeCompositeDown
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.FunctorIsoUliftRecovery
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.IsoSquareTransport
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.FunctorSpaceDownObjects

/-!
概要：native cospan の四射の値比較と元の可換同型の整合を元の小宇宙へ移す。
方針：元の可換式を同じ通常の下降関手で写し、明示した四端点と指定値で戻す。
規約：元の指定可換同型を保持。使われ方：共通引き戻しの左右の指定同型の底の整合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.F2
variable {B : SSet.{u}} [Quasicategory B]
  (F X Y Z : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
  (C : CoherentTransformationCospanCone F X Y Z)
local notation "cl" => coherentTransformationTotalMap F X C.toLeft
local notation "cr" => coherentTransformationTotalMap F Y C.toRight
local notation "cf" => coherentTransformationTotalMap X Z C.fromLeft
local notation "cg" => coherentTransformationTotalMap Y Z C.fromRight

/-- 元の四射の指定合成比較と native な可換同型は、元の小宇宙でも同じ可換式を満たす。 -/
lemma coherentCospanConeNativePathDownIso_comparison :
    coherentTotalMapNativeCompositeDownIso F X Z cl cf ≪≫
      coherentCospanConeValuePathIso F X Y Z C =
    coherentCospanConeNativePathDownIso F X Y Z C ≪≫
      coherentTotalMapNativeCompositeDownIso F Y Z cr cg := by
  let D := functorSpaceDown.{u, u + 1}
    (spaceInfinityObject (coherentDiagramTotalVertex F)).obj
    (spaceInfinityObject (coherentDiagramTotalVertex Z)).obj
  have h := congrArg (fun e => D.mapIso e)
    (coherentCospanConeNativeValuePathIso_comparison F X Y Z C)
  simp only [Functor.mapIso_trans] at h
  have hp : HEq (coherentCospanConeValuePathIso F X Y Z C)
      (D.mapIso (coherentCospanConeValuePathIso F X Y Z C).ulift) := by
    have hr := functorIsoDown_ulift_iso (coherentCospanConeValuePathIso F X Y Z C)
    exact heq_of_eq (hr.symm.trans
      (functorIsoDown_eq_mapIso (coherentCospanConeValuePathIso F X Y Z C).ulift))
  have ha := functorSpaceDown_obj_comp.{u, u + 1}
    (coherentTotalMapNativeValue F X cl) (coherentTotalMapNativeValue X Z cf)
  have hb := functorSpaceDown_obj_map.{u, u + 1}
    (coherentTotalVertexMap F X cl ≫ coherentTotalVertexMap X Z cf)
  have hc := functorSpaceDown_obj_comp.{u, u + 1}
    (coherentTotalMapNativeValue F Y cr) (coherentTotalMapNativeValue Y Z cg)
  have hd := functorSpaceDown_obj_map.{u, u + 1}
    (coherentTotalVertexMap F Y cr ≫ coherentTotalVertexMap Y Z cg)
  exact iso_square_transport _ _ _ _ _ _ _ _ h ha hb hc hd
    (coherentTotalMapNativeCompositeDownIso_heq_map F X Z cl cf) hp
    (coherentCospanConeNativePathDownIso_heq_map F X Y Z C)
    (coherentTotalMapNativeCompositeDownIso_heq_map F Y Z cr cg)

end SerrePositivity.InfinityCategories.F2
