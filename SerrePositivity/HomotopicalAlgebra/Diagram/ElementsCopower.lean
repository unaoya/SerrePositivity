module

public import Mathlib.CategoryTheory.Elements
public import Mathlib.CategoryTheory.Limits.Shapes.Products

/-!
概要：要素で添字付けた余積図式の余錐と、要素圏上の余錐の同値。
方針：余積の挿入とdescを用い、全ての添字射に関する自然性を確認する。
使われ方：HTT 4.2.4.4、RR02(a)の自由評価の余積を要素圏へ移す比較。
規約：元の係数と射を保つ通常の余錐の同値。導来比較とは区別する。
-/

@[expose] public noncomputable section
universe w v u
open CategoryTheory CategoryTheory.Limits
namespace SerrePositivity.DiagramModel.ElementsCopower
variable {K : Type w} [SmallCategory K]
  {C : Type u} [Category.{v} C] [HasCoproducts.{w} C]
  (F : K ⥤ Type w) (B : K ⥤ C)

/-- 各値に、指定された要素集合で添字付けた余積を取る。 -/
def diagram : K ⥤ C where
  obj k := ∐ fun _ : F.obj k => B.obj k
  map {k l} f := Sigma.map' (F.map f) (fun _ => B.map f)
  map_id k := by
    apply Sigma.hom_ext
    intro x
    simp
  map_comp f g := by
    apply Sigma.hom_ext
    intro x
    simp [Category.assoc, Functor.map_comp_apply]

/-- 余積の各挿入に制限した、同じ係数の要素圏上の余錐。 -/
def toElements (Y : C) (a : diagram F B ⟶ (Functor.const K).obj Y) :
    Functor.Elements.π F ⋙ B ⟶ (Functor.const F.Elements).obj Y where
  app e := Sigma.ι (fun _ : F.obj e.obj => B.obj e.obj) e.val ≫ a.app e.obj
  naturality e e' f := by
    have h := congrArg
      (fun z => Sigma.ι (fun _ : F.obj e.obj => B.obj e.obj) e.val ≫ z)
      (a.naturality f.hom)
    simpa [diagram, Category.assoc, f.map_val] using h

/-- 要素圏の余錐を、元の余積の普遍性で束ねる。 -/
def fromElements (Y : C)
    (a : Functor.Elements.π F ⋙ B ⟶ (Functor.const F.Elements).obj Y) :
    diagram F B ⟶ (Functor.const K).obj Y where
  app k := Sigma.desc (fun x => a.app (F.elementsMk k x))
  naturality k l f := by
    apply Sigma.hom_ext
    intro x
    have h := a.naturality
      (show F.elementsMk k x ⟶ F.elementsMk l (F.map f x) from
        { hom := f, map_val := rfl })
    simpa [diagram, Category.assoc] using h

/-- 二つの構成は、全ての添字射を保って互いに逆。 -/
def homEquiv (Y : C) :
    (diagram F B ⟶ (Functor.const K).obj Y) ≃
      (Functor.Elements.π F ⋙ B ⟶ (Functor.const F.Elements).obj Y) where
  toFun := toElements F B Y
  invFun := fromElements F B Y
  left_inv a := by
    apply NatTrans.ext
    funext k
    apply Sigma.hom_ext
    intro x
    simp [toElements, fromElements]
  right_inv a := by
    apply NatTrans.ext
    funext e
    simp [toElements, fromElements]

/-- 余錐の標的の後合成と両立する。 -/
lemma homEquiv_naturality {Y Z : C} (f : Y ⟶ Z)
    (a : diagram F B ⟶ (Functor.const K).obj Y) :
    homEquiv F B Z (a ≫ (Functor.const K).map f) =
      homEquiv F B Y a ≫ (Functor.const F.Elements).map f := by
  apply NatTrans.ext
  funext e
  exact (Category.assoc _ _ _).symm

end SerrePositivity.DiagramModel.ElementsCopower
