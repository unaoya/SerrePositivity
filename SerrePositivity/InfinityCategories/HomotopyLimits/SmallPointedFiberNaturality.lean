module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentTransformationTotalMap
public import SerrePositivity.InfinityCategories.F1.LeftUnstraighteningFiberTransport

/-!
概要：小さい unstraightening の fiber を普遍 pointed fiber に移し、元の変換作用を保持する。
方針：縮小の fiber 同型と引き戻しの fiber 同型を合成する。
規約：変換頂点は指定されたもの。使われ方：積比較の同値性を元の宇宙へ反映する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
variable {B : SSet.{u}}

/-- 小さい fiber の宇宙持ち上げを、同じ図式の値の普遍 pointed fiber に同定する。 -/
def smallPointedFiberIso
    (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}) (b : B _⦋0⦌) :
    (SSet.uliftFunctor.{u + 1, u}).obj
        (vertexFiber (smallLeftUnstraighteningProjection F) b) ≅
      vertexFiber pointedSpaceProjection (F.app (Opposite.op ⦋0⦌) (ULift.up b)) :=
  smallLeftUnstraighteningFiberIso F b ≪≫ leftUnstraighteningFiberIso F (ULift.up b)

/-- 元の指定変換の小さい fiber の作用は、同じ変換の pointed fiber 作用と厳密に可換。 -/
lemma smallPointedFiberIso_naturality
    (F G : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
    (x : (leftUnstraighteningTransformationSpace F G) _⦋0⦌) (b : B _⦋0⦌) :
    (SSet.uliftFunctor.{u + 1, u}).map
      (vertexFiberMap (smallLeftUnstraighteningProjection F) (smallLeftUnstraighteningProjection G)
        (F2.coherentTransformationTotalMap F G x)
        (F2.coherentTransformationTotalMap_projection F G x) b) ≫
          (smallPointedFiberIso G b).hom =
      (smallPointedFiberIso F b).hom ≫ leftUnstraighteningPointedFiberMap F G
        (leftUnstraighteningMappingVertexMap F G x).val
        (leftUnstraighteningMappingVertexMap F G x).property (ULift.up b) := by
  have h := smallLeftUnstraighteningOverMap_fiber_naturality F G
    (leftUnstraighteningMappingVertexMap F G x).val
    (leftUnstraighteningMappingVertexMap F G x).property b
  change (SSet.uliftFunctor.{u + 1, u}).map
    (vertexFiberMap _ _ (F2.coherentTransformationTotalMap F G x)
      (F2.coherentTransformationTotalMap_projection F G x) b) ≫
        (smallLeftUnstraighteningFiberIso G b).hom = _ at h
  simpa only [smallPointedFiberIso, Iso.trans_hom, leftUnstraighteningPointedFiberMap,
    Category.assoc, Iso.hom_inv_id_assoc] using
      congrArg (fun k ↦ k ≫ (leftUnstraighteningFiberIso G (ULift.up b)).hom) h

end SerrePositivity.InfinityCategories.HomotopyLimits
