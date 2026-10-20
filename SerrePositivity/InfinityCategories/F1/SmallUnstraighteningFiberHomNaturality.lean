module

public import SerrePositivity.InfinityCategories.F1.SmallLeftUnstraighteningMappingSpace
public import SerrePositivity.InfinityCategories.F1.SmallLeftUnstraighteningFiber
public import SerrePositivity.InfinityCategories.F1.RelativeFunctorOverIsoFiberHom
public import SerrePositivity.InfinityCategories.F1.UniverseRelativeFunctorFiberHom

/-!
概要：小さい unstraightening の相対 Hom の同型は、同じ fiber の実際の全 Hom 作用を保つ。
方針：全空間の縮小同型と宇宙移送の二つの共役を、同じ fiber の縮小同型へまとめる。
規約：対象ごとの射だけでなく、全パラメーターの内部 Hom への射として照合する。
使われ方：同じ Yoneda 恒等点評価と c1 の普遍輸送比較の接続。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 小さい相対 Hom の同型は、元の fiber Hom 作用と同じ fiber の同型によって厳密に可換。 -/
lemma smallLeftUnstraighteningRelativeFunctorIso_fiberHom {B : SSet.{u}}
    (F G : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}) (b : B _⦋0⦌) :
    (smallLeftUnstraighteningRelativeFunctorIso F G).hom ≫
      relativeFunctorFiberHom (leftUnstraighteningProjection F)
        (leftUnstraighteningProjection G) (ULift.up b) =
    (SSet.uliftFunctor.{u + 1, u}).map
        (relativeFunctorFiberHom (smallLeftUnstraighteningProjection F)
          (smallLeftUnstraighteningProjection G) b) ≫
      (uliftFunctorSpaceIso.{u, u + 1}
        (vertexFiber (smallLeftUnstraighteningProjection F) b)
        (vertexFiber (smallLeftUnstraighteningProjection G) b)).hom ≫
      (pre (smallLeftUnstraighteningFiberIso F b).inv).app
        ((SSet.uliftFunctor.{u + 1, u}).obj
          (vertexFiber (smallLeftUnstraighteningProjection G) b)) ≫
      (ihom (vertexFiber (leftUnstraighteningProjection F) (ULift.up b))).map
        (smallLeftUnstraighteningFiberIso G b).hom := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro f
  apply CategoryTheory.Functor.functorHom_ext
  intro d α
  apply ConcreteCategory.hom_ext
  intro x
  apply Subtype.ext
  rfl

end SerrePositivity.InfinityCategories
