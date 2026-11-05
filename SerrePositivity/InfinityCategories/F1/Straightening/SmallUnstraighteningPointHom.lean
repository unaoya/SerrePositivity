module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias
public import SerrePositivity.InfinityCategories.F1.Straightening.SmallUnstraighteningPointAction
public import SerrePositivity.InfinityCategories.F1.Transport.PointedTransformationPointHom

/-! # 同じ小さい unstraightening の実写像の点の射は、指定二胞体の成分との合成 -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Fibration
end SerrePositivity.KST.Fibration
namespace SerrePositivity.InfinityCategories.F1.Straightening
open SerrePositivity.KST.Fibration

/-- 元の小さい実 fiber 点を同じ実写像で送った点の射を、元の比較成分で計算する。 -/
theorem smallUnstraighteningFunctorHom_pointHom {B : SSet.{u}}
    {F G : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}}
    (a : FunctorHom F G) (b : B _⦋0⦌)
    (v : (vertexFiber (smallLeftUnstraighteningProjection F) b) _⦋0⦌) :
    cosliceFiberPointHom (smallUnstraighteningPointedImage F b v) ≫
      functorHomEvaluate a (ULift.up b) =
      cosliceFiberPointHom (smallUnstraighteningPointedImage G b
        ((vertexFiberMap (smallLeftUnstraighteningProjection F)
          (smallLeftUnstraighteningProjection G) (smallUnstraighteningFunctorHom a)
          (smallUnstraighteningFunctorHom_projection a) b).app (Opposite.op ⦋0⦌) v)) :=
  (pointedFunctorHomPointHom a b (smallUnstraighteningPointedImage F b v)).trans
    (congrArg cosliceFiberPointHom (smallUnstraighteningFunctorHom_pointAction F G b a v))

end SerrePositivity.InfinityCategories.F1.Straightening

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.smallUnstraighteningFunctorHom_pointHom := _root_.SerrePositivity.InfinityCategories.F1.Straightening.smallUnstraighteningFunctorHom_pointHom
