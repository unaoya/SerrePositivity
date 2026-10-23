module

public import SerrePositivity.InfinityCategories.F1.RelativeFunctorPostUncurry
public import SerrePositivity.InfinityCategories.F2.Presentable.FiniteOverPresentable

/-!
概要：任意の底上の対象を標的とする相対 Hom 関手と、底上のパラメータ付き射の普遍性。
方針：F1 の相対後合成の全自然な作用を関手に束ね、相対 curry と uncurry を往復する。
規約：底と全空間の充填性は不要。相対 Hom は元の F1 の単体集合そのもの。
使われ方：有限始域の相対 Hom の filtered 余極限保存。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
namespace SerrePositivity.InfinityCategories.F2.Presentable

/-- 底上の対象を可変の標的とする、元の相対 Hom の単体集合値関手。 -/
def relativeOverHomFunctor {B : SSet.{u}} (A : Over B) : Over B ⥤ SSet.{u} where
  obj X := relativeFunctorSpace X.hom A.hom
  map f := HomotopyLimits.relativeFunctorPost _ _ f.left f.w A.hom
  map_id X := relativeFunctorPost_id X.hom A.hom
  map_comp f g := (relativeFunctorPost_comp _ _ _ f.left f.w g.left g.w A.hom).symm

/-- 右パラメータ付き始域を、同じ底上の対象として保持する。 -/
def overTensorParameter {B : SSet.{u}} (A : Over B) (T : SSet.{u}) : Over B :=
  Over.mk (fst A.left T ≫ A.hom)

/-- 相対 Hom への全パラメータ付き射と、元の底上の射の実際の全単射。 -/
def relativeOverHomTensorEquiv {B : SSet.{u}} (A X : Over B) (T : SSet.{u}) :
    (T ⟶ (relativeOverHomFunctor A).obj X) ≃ (overTensorParameter A T ⟶ X) where
  toFun f := Over.homMk (relativeFunctorUncurry f) (relativeFunctorUncurry_projection f)
  invFun f := relativeFunctorCurry f.left f.w
  left_inv f := by
    apply relativeFunctorUncurry_injective X.hom A.hom
    exact relativeFunctorUncurry_curry _ _
  right_inv f := by
    apply Over.OverMorphism.ext
    exact relativeFunctorUncurry_curry _ _

/-- この全単射は、任意の底上の標的の射による後合成と厳密に両立する。 -/
lemma relativeOverHomTensorEquiv_naturality {B : SSet.{u}} (A : Over B) (T : SSet.{u})
    {X Y : Over B} (f : X ⟶ Y) (t : T ⟶ (relativeOverHomFunctor A).obj X) :
    relativeOverHomTensorEquiv A Y T (t ≫ (relativeOverHomFunctor A).map f) =
      relativeOverHomTensorEquiv A X T t ≫ f := by
  apply Over.OverMorphism.ext
  exact relativeFunctorPost_uncurry X.hom Y.hom f.left f.w A.hom t

end SerrePositivity.InfinityCategories.F2.Presentable
