module
public import SerrePositivity.KST.Fibration.SmallUnstraighteningPointAction
public import SerrePositivity.KST.Fibration.PointedTransformationPointHom

/-! # 同じ小さい unstraightening の実写像の点の射は、指定二胞体の成分との合成 -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Fibration

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

end SerrePositivity.KST.Fibration
