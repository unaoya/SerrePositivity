module

public import Mathlib.CategoryTheory.Preadditive.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.Algebra.Group.Equiv.Basic

/-!
概要：余積からの Hom と成分ごとの Hom の加法的な同値。
方針：余積の挿入射と普遍的な降下写像を互いの逆にする。
規約：有限性は要求しない。
使われ方：TT §3・§8、Toën §3.2 の自由 Čech の Hom と切断の積の比較。
-/

@[expose] public section
noncomputable section
universe u v w
open CategoryTheory Limits Preadditive
namespace SerrePositivity.KST.DerivedGeometry
variable {A : Type u} [Category.{v} A] [Preadditive A]
  {ι : Type w} (M : ι → A) [HasCoproduct M] (N : A)

/--
概要：余積からの射は成分ごとの射の族と加法的に同値。
方針：挿入射との合成と余積の降下の普遍性を使う。
規約：係数の線形性ではなく加法群として比較する。
使われ方：TT §3・§8、Toën §3.2 の自由 Čech の Hom 比較。
-/
def coproductHomAddEquiv : ((∐ M) ⟶ N) ≃+ (∀ i, M i ⟶ N) where
  toFun f i := Sigma.ι M i ≫ f
  invFun f := Sigma.desc f
  left_inv f := Sigma.hom_ext _ _ (fun i => Sigma.ι_comp_desc _ i)
  right_inv f := funext (fun i => Sigma.ι_comp_desc f i)
  map_add' f g := funext (fun i => comp_add _ _ _ (Sigma.ι M i) f g)

end SerrePositivity.KST.DerivedGeometry
