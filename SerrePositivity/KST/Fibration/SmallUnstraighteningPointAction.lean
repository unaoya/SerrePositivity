module
public import SerrePositivity.KST.Fibration.SmallUnstraighteningFunctorHom
public import SerrePositivity.InfinityCategories.F1.SmallUnstraighteningPointFiberEvaluation
public import SerrePositivity.InfinityCategories.F1.LeftUnstraighteningFiberFamily

/-! # 指定した小さい fiber 点での同じ全変換空間の作用を、元の pointed-space 作用と結ぶ -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Fibration
variable {B : SSet.{u}}
  (F G : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}) (b : B _⦋0⦌)

/-- 元の小さい fiber 点を、同じ縮小同型と引き戻し同型で pointed-space fiber に表示する。 -/
def smallUnstraighteningPointedImage
    (v : (vertexFiber (smallLeftUnstraighteningProjection F) b) _⦋0⦌) :
    (vertexFiber pointedSpaceProjection (F.app (Opposite.op ⦋0⦌) (ULift.up b))) _⦋0⦌ :=
  (leftUnstraighteningFiberIso F (ULift.up b)).hom.app (Opposite.op ⦋0⦌)
    ((smallLeftUnstraighteningFiberIso F b).hom.app (Opposite.op ⦋0⦌) (ULift.up v))

/-- 元の全変換空間の指定点評価は、小さい相対 Hom の同じ点評価の厳密な移送。 -/
theorem smallUnstraighteningPointAction_eq
    (v : (vertexFiber (smallLeftUnstraighteningProjection F) b) _⦋0⦌) :
    leftUnstraighteningMappingFiberHom F G (ULift.up b) ≫
      evaluateFunctorAt (smallUnstraighteningPointedImage F b v) =
      leftUnstraighteningMappingSpaceMap F G ≫
        (smallLeftUnstraighteningRelativeFunctorIso F G).inv ≫
        (SSet.uliftFunctor.{u + 1, u}).map
          (relativeFunctorFiberHom (smallLeftUnstraighteningProjection F)
            (smallLeftUnstraighteningProjection G) b ≫ evaluateFunctorAt v) ≫
        (smallLeftUnstraighteningFiberIso G b).hom ≫
        (leftUnstraighteningFiberIso G (ULift.up b)).hom := by
  let e := smallLeftUnstraighteningRelativeFunctorIso F G
  let w := (smallLeftUnstraighteningFiberIso F b).hom.app (Opposite.op ⦋0⦌) (ULift.up v)
  let z := smallUnstraighteningPointedImage F b v
  have hz : (leftUnstraighteningFiberIso F (ULift.up b)).inv.app (Opposite.op ⦋0⦌) z = w :=
    congrArg (fun m => m.app (Opposite.op ⦋0⦌) w)
      (leftUnstraighteningFiberIso F (ULift.up b)).hom_inv_id
  have hp := smallLeftUnstraighteningRelativeFunctorIso_pointEvaluation F G b v
  have hb : relativeFunctorFiberHom (leftUnstraighteningProjection F)
      (leftUnstraighteningProjection G) (ULift.up b) ≫ evaluateFunctorAt w =
      e.inv ≫ (SSet.uliftFunctor.{u + 1, u}).map
        (relativeFunctorFiberHom (smallLeftUnstraighteningProjection F)
          (smallLeftUnstraighteningProjection G) b ≫ evaluateFunctorAt v) ≫
        (smallLeftUnstraighteningFiberIso G b).hom := by
    calc
      _ = e.inv ≫ (e.hom ≫ relativeFunctorFiberHom (leftUnstraighteningProjection F)
          (leftUnstraighteningProjection G) (ULift.up b) ≫ evaluateFunctorAt w) :=
        (e.inv_hom_id_assoc _).symm
      _ = _ := by rw [hp]
  rw [leftUnstraighteningMappingFiberHom]
  simp only [Category.assoc]
  rw [evaluateFunctorAt_post]
  rw [← Category.assoc _ (evaluateFunctorAt z)
    (leftUnstraighteningFiberIso G (ULift.up b)).hom, evaluateFunctorAt_pre, hz]
  have he := congrArg (fun m => leftUnstraighteningMappingSpaceMap F G ≫ m ≫
    (leftUnstraighteningFiberIso G (ULift.up b)).hom) hb
  simpa only [Category.assoc] using he

/-- 同じ比較二胞体の実写像の fiber 作用は、同じ全変換空間の指定パラメーターでの作用。 -/
theorem smallUnstraighteningFunctorHom_pointAction (a : FunctorHom F G)
    (v : (vertexFiber (smallLeftUnstraighteningProjection F) b) _⦋0⦌) :
    (leftUnstraighteningMappingFiberHom F G (ULift.up b) ≫
      evaluateFunctorAt (smallUnstraighteningPointedImage F b v)).app (Opposite.op ⦋0⦌)
        (smallUnstraighteningHomParameter a) =
      smallUnstraighteningPointedImage G b
        ((vertexFiberMap (smallLeftUnstraighteningProjection F)
          (smallLeftUnstraighteningProjection G) (smallUnstraighteningFunctorHom a)
          (smallUnstraighteningFunctorHom_projection a) b).app (Opposite.op ⦋0⦌) v) := by
  have he := congrArg (fun m => m.app (Opposite.op ⦋0⦌)
    (smallUnstraighteningHomParameter a)) (smallUnstraighteningPointAction_eq F G b v)
  change _ = (leftUnstraighteningFiberIso G (ULift.up b)).hom.app (Opposite.op ⦋0⦌)
    ((smallLeftUnstraighteningFiberIso G b).hom.app (Opposite.op ⦋0⦌)
      (ULift.up ((relativeFunctorFiberHom (smallLeftUnstraighteningProjection F)
        (smallLeftUnstraighteningProjection G) b ≫ evaluateFunctorAt v).app
          (Opposite.op ⦋0⦌) (smallUnstraighteningHomVertex a)))) at he
  have hv : (relativeFunctorFiberHom (smallLeftUnstraighteningProjection F)
      (smallLeftUnstraighteningProjection G) b ≫ evaluateFunctorAt v).app
      (Opposite.op ⦋0⦌) (smallUnstraighteningHomVertex a) =
      (vertexFiberMap (smallLeftUnstraighteningProjection F)
        (smallLeftUnstraighteningProjection G) (smallUnstraighteningFunctorHom a)
        (smallUnstraighteningFunctorHom_projection a) b).app (Opposite.op ⦋0⦌) v := by
    rw [← smallUnstraighteningFunctorHom_vertex]
    change (evaluateFunctorAt v).app (Opposite.op ⦋0⦌)
      ((relativeFunctorFiberHom _ _ b).app (Opposite.op ⦋0⦌)
        (relativeFunctorVertex _ _ (smallUnstraighteningFunctorHom a)
          (smallUnstraighteningFunctorHom_projection a))) = _
    rw [relativeFunctorFiberHom_vertex, evaluateFunctorAt_functorVertex]
  exact he.trans (congrArg (fun s =>
    (leftUnstraighteningFiberIso G (ULift.up b)).hom.app (Opposite.op ⦋0⦌)
      ((smallLeftUnstraighteningFiberIso G b).hom.app (Opposite.op ⦋0⦌) (ULift.up s))) hv)

end SerrePositivity.KST.Fibration
