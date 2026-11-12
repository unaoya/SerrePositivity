module
public import SerrePositivity.HomologicalAlgebra.CochainProductTotalComponents
public import Mathlib.CategoryTheory.ConcreteCategory.Elementwise

/-!
概要：非負余鎖二重複体の積全複体の各次数を、成分加群の積との線形同値で表示する。
方針：指定射影と積の普遍性で二つの逆写像を作り、同じ各成分で相互逆を検証する。
規約：二重複体の内部次数は非有界。位相的な完備化は用いない。
使われ方：HA 1.2.4、G10 の重み end の次数ごとの Hom 比較。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SerrePositivity.DifferentialGraded
open scoped SerrePositivity.HomologicalAlgebra.ProductTotal
namespace SerrePositivity.HomologicalAlgebra.CochainProductTotal
variable {A : Type u} [CommRing A]
variable (K : CochainComplex (Complex A) ℕ)

/-- 成分の加群積から、元の指定積全複体の次数 q への線形射。 -/
def familyLift (q : ℤ) :
    ModuleCat.of A (∀ n : ℕ, (K.X n).X (q-n)) ⟶
      ((cochainProductTotalizationFunctor (ModuleCat.{u} A)).obj K).X q :=
  componentLift K q (fun n => ModuleCat.ofHom (LinearMap.proj n))

/-- 指定成分による、全次数 q の実際の線形同値。 -/
def componentsLinearEquiv (q : ℤ) :
    ((cochainProductTotalizationFunctor (ModuleCat.{u} A)).obj K).X q ≃ₗ[A]
      (∀ n : ℕ, (K.X n).X (q-n)) where
  toFun z n := componentπ K n q z
  invFun f := familyLift K q f
  left_inv z := by
    apply Concrete.isLimit_ext _ (componentFanIsLimit K q)
    intro n
    exact congrArg (fun f => f (fun m => componentπ K m q z))
      (componentLift_π K q (fun m => ModuleCat.ofHom (LinearMap.proj m)) n.as)
  right_inv f := by
    funext n
    exact congrArg (fun g => g f)
      (componentLift_π K q (fun m => ModuleCat.ofHom (LinearMap.proj m)) n)
  map_add' x y := by
    funext n
    exact (componentπ K n q).hom.map_add x y
  map_smul' r x := by
    funext n
    exact (componentπ K n q).hom.map_smul r x

end SerrePositivity.HomologicalAlgebra.CochainProductTotal
