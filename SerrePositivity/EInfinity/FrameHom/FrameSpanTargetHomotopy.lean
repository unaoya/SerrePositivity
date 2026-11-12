module

public import SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.FrameSpanNerve
public import SerrePositivity.EInfinity.FrameHom.FrameSpanNaturality
public import SerrePositivity.HomotopicalAlgebra.Simplicial.AnodyneHomotopyLocalization

/-!
# 元の frame の右脚比較の全単体の nerve ホモトピー

概要：同じ端点の右脚比較を元の要素圏の持ち上げからのホモトピーにする。
方針：元の自然変換の区間関手に全射列と区間パラメータを代入する。
規約：要素圏と元の圏の異なる Hom 宇宙を保持する。
使われ方：元の終域への frame Hom と既存 Map^h の比較の一致。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.EInfinity.FrameHom
open CategoryTheory MonoidalCategory SerrePositivity.HomotopyFunctionComplex
variable {C : Type u} [Category.{v} C] (L R : MorphismProperty C)
  {X Y Z Z' : C} (A : SimplexCategory ⥤ C)
  (p : A ⟶ (Functor.const SimplexCategory).obj X) (hp : ∀ n, L (p.app n))
  (j : Y ⟶ Z) (hj : R j) (j' : Y ⟶ Z') (hj' : R j')
  (β : Z ⟶ Z') (hβ : j ≫ β = j')

def frameSpanTargetIndexMap :
    ULiftHom.{max u v} (((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom A).obj Z).Elements)ᵒᵖ ⥤
      ULiftHom.{max u v} (((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom A).obj Z').Elements)ᵒᵖ :=
  ULiftHom.down.{0, v, max u v} ⋙ ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom A).map β).mapElements.op ⋙ ULiftHom.up

def frameSpanTargetHomotopyMap :
    nerve (ULiftHom.{max u v} (((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom A).obj Z).Elements)ᵒᵖ) ⊗
      SSet.stdSimplex.{max u v}.obj (SimplexCategory.mk 1) ⟶
        nerve (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.Object L R X Y) where
  app _ := ↾fun a =>
    ((SSet.stdSimplex.objEquiv a.2).toOrderHom.monotone.functor.prod'
      (a.1 ⋙ ULiftHom.down.{0, v, max u v})) ⋙
        Functor.uncurry.obj (ComposableArrows.mk₁
          (frameSpanTargetComparison L R p hp j hj j' hj' β hβ))
  naturality _ _ _ := rfl

def frameSpanTargetHomotopy : SSet.Homotopy (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.frameElementSpanNerveMap L R A p hp j hj)
    (nerveMap (frameSpanTargetIndexMap A β) ≫ _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.frameElementSpanNerveMap L R A p hp j' hj') where
  h := frameSpanTargetHomotopyMap L R A p hp j hj j' hj' β hβ
  h₀ := by
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro σ
    refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
    intro a b f
    change 𝟙 _ ≫ (frameElementSpanFunctor L R A p hp j hj).map
        (ULiftHom.down.map (σ.map f)) =
      eqToHom rfl ≫ (frameElementSpanFunctor L R A p hp j hj).map
        (ULiftHom.down.map (σ.map f)) ≫ eqToHom rfl
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  h₁ := by
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro σ
    refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
    intro a b f
    change 𝟙 _ ≫ (frameElementSpanFunctor L R A p hp j' hj').map
        (((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom A).map β).mapElements.op.map
          (ULiftHom.down.map (σ.map f))) =
      eqToHom rfl ≫ (frameElementSpanFunctor L R A p hp j' hj').map
        (((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom A).map β).mapElements.op.map
          (ULiftHom.down.map (σ.map f))) ≫ eqToHom rfl
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  rel := by
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro x
    exact False.elim x.1.property

end SerrePositivity.EInfinity.FrameHom
