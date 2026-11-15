module

public import SerrePositivity.HomotopicalAlgebra.Diagram.ElementsCopowerWeightedHom

/-!
概要：余積frameの実現を、要素圏上の同じ係数の実現へ移す。
方針：全単体のHom同値を両側の指定随伴で挟み、余米田で同型にする。
使われ方：HTT 4.2.4.4、RR02(a)の自由評価の実現の表示。
規約：重みは射影による制限であり、別の弱同値模型に置き換えない。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe w u
open CategoryTheory CategoryTheory.Limits
namespace SerrePositivity.DiagramModel.ElementsCopower
variable {K : Type w} [SmallCategory K]
  {C : Type u} [Category.{w} C] [HasColimitsOfSize.{w, w} C]
  (F : K ⥤ Type w) (B : K ⥤ SimplexCategory ⥤ C)
  (W : Kᵒᵖ ⥤ SSet.{w})

/-- 要素圏への制限は、標的への後合成と両立する。 -/
lemma weightedHomEquiv_target_naturality {Y Z : C} (f : Y ⟶ Z)
    (a : W ⟶ (FrameWeightRealization.hom K (frames F B)).obj Y) :
    weightedHomEquiv F B W Z (a ≫ (FrameWeightRealization.hom K (frames F B)).map f) =
      weightedHomEquiv F B W Y a ≫
        (FrameWeightRealization.hom F.Elements (Functor.Elements.π F ⋙ B)).map f := by
  ext e n z
  exact (Category.assoc _ _ _).symm

/-- 両側の指定実現随伴による、実現からの射の同値。 -/
def realizationHomEquiv (Y : C) :
    ((FrameWeightRealization.functor K (frames F B)).obj W ⟶ Y) ≃
      ((FrameWeightRealization.functor F.Elements (Functor.Elements.π F ⋙ B)).obj
        ((Functor.Elements.π F).op ⋙ W) ⟶ Y) :=
  ((FrameWeightRealization.adjunction K (frames F B)).homEquiv W Y).trans
    ((weightedHomEquiv F B W Y).trans
      ((FrameWeightRealization.adjunction F.Elements (Functor.Elements.π F ⋙ B)).homEquiv
        ((Functor.Elements.π F).op ⋙ W) Y).symm)

lemma realizationHomEquiv_naturality {Y Z : C} (f : Y ⟶ Z)
    (a : (FrameWeightRealization.functor K (frames F B)).obj W ⟶ Y) :
    realizationHomEquiv F B W Z (a ≫ f) = realizationHomEquiv F B W Y a ≫ f := by
  dsimp only [realizationHomEquiv, Equiv.trans_apply]
  rw [Adjunction.homEquiv_naturality_right, weightedHomEquiv_target_naturality,
    Adjunction.homEquiv_naturality_right_symm]

/-- 実現そのものの同型。同じ係数と制限重みを保つ。 -/
def realizationIso :
    (FrameWeightRealization.functor K (frames F B)).obj W ≅
      (FrameWeightRealization.functor F.Elements (Functor.Elements.π F ⋙ B)).obj
        ((Functor.Elements.π F).op ⋙ W) :=
  (Coyoneda.fullyFaithful.preimageIso
    (NatIso.ofComponents (fun Y => Equiv.toIso (realizationHomEquiv F B W Y))
      (by intro Y Z f; ext a; exact realizationHomEquiv_naturality F B W f a))).unop.symm

end SerrePositivity.DiagramModel.ElementsCopower
