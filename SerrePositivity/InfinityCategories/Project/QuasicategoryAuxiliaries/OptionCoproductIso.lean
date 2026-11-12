module

public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts

/-!
概要：Option で添字付けた余積を、一つの因子と残りの余積へ分解する。
方針：余積の包含と普遍射を両方向に組み合わせる。
規約：任意の圏と添字宇宙について、実際の余積の同型を与える。
使われ方：形状 pushout に閉じる性質を有限余積に対して帰納する。
-/

@[expose] public section
noncomputable section
universe v u w
open CategoryTheory Limits
namespace SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries

/-- Option 上の余積の指定された二項分解。 -/
def optionCoproductIso {C : Type u} [Category.{v} C] {J : Type w}
    (F : Option J → C) [HasCoproduct F] [HasCoproduct (fun j => F (some j))]
    [HasBinaryCoproduct (F none) (∐ fun j => F (some j))] :
    (∐ F) ≅ (F none ⨿ (∐ fun j => F (some j))) where
  hom := Sigma.desc (fun o => Option.casesOn o coprod.inl
    (fun j => Sigma.ι (fun k => F (some k)) j ≫ coprod.inr))
  inv := coprod.desc (Sigma.ι F none) (Sigma.desc (fun j => Sigma.ι F (some j)))
  hom_inv_id := by
    apply Sigma.hom_ext
    intro o
    cases o <;> simp [Category.assoc]
  inv_hom_id := by
    apply coprod.hom_ext
    · simp [Category.assoc]
    · apply Sigma.hom_ext
      intro j
      simp [Category.assoc]

end SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries
