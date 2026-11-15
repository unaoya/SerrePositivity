module

public import SerrePositivity.HomotopicalAlgebra.Diagram.ElementsCopowerRealization

/-!
概要：要素圏への実現同型は、指定したHom同値を回収する。
方針：余米田の充満忠実性のmap_preimageを、任意の標的と射で評価する。
使われ方：HTT 4.2.4.4、RR02(a)で元の増大射を保つことの照合。
規約：実現同型の選択を変更せず、その逆との合成を評価する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe w u
open CategoryTheory CategoryTheory.Limits
namespace SerrePositivity.DiagramModel.ElementsCopower
variable {K : Type w} [SmallCategory K]
  {C : Type u} [Category.{w} C] [HasColimitsOfSize.{w, w} C]
  (F : K ⥤ Type w) (B : K ⥤ SimplexCategory ⥤ C) (W : Kᵒᵖ ⥤ SSet.{w})

/-- 指定実現同型の逆との合成は、元の随伴によるHom同値そのもの。 -/
lemma realizationIso_inv_comp (Y : C)
    (f : (FrameWeightRealization.functor K (frames F B)).obj W ⟶ Y) :
    (realizationIso F B W).inv ≫ f = realizationHomEquiv F B W Y f := by
  let e : coyoneda.obj (Opposite.op ((FrameWeightRealization.functor K (frames F B)).obj W)) ≅
      coyoneda.obj (Opposite.op
        ((FrameWeightRealization.functor F.Elements (Functor.Elements.π F ⋙ B)).obj
          ((Functor.Elements.π F).op ⋙ W))) :=
    NatIso.ofComponents (fun Y => Equiv.toIso (realizationHomEquiv F B W Y))
      (by intro Y Z f; ext a; exact realizationHomEquiv_naturality F B W f a)
  have h := Coyoneda.fullyFaithful.map_preimage e.hom
  exact congrArg (fun z => z.app Y f) h

end SerrePositivity.DiagramModel.ElementsCopower
