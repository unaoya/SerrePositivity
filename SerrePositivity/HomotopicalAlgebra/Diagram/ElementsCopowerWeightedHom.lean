module

public import SerrePositivity.HomotopicalAlgebra.Diagram.ElementsCopowerFrames

/-!
概要：余積frameの重み付きHomと要素圏上の重み付きHomの同値。
方針：各単体でSigma.descを取り、余積の挿入で自然性と両逆を検査する。
使われ方：HTT 4.2.4.4、RR02(a)の実現の要素圏表示。
規約：同じ重みを射影に沿って制限し、単体と添字の両方の自然性を保つ。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe w u
open CategoryTheory CategoryTheory.Limits
namespace SerrePositivity.DiagramModel.ElementsCopower
variable {K : Type w} [SmallCategory K]
  {C : Type u} [Category.{w} C] [HasColimitsOfSize.{w, w} C]
  (F : K ⥤ Type w) (B : K ⥤ SimplexCategory ⥤ C)
  (W : Kᵒᵖ ⥤ SSet.{w}) (Y : C)

/-- 各単体の射を同じ余積に束ね、重み付きHomへ戻す。 -/
def weightedHomFromElements
    (a : (Functor.Elements.π F).op ⋙ W ⟶
      (FrameWeightRealization.hom F.Elements (Functor.Elements.π F ⋙ B)).obj Y) :
    W ⟶ (FrameWeightRealization.hom K (frames F B)).obj Y where
  app k := {
    app n := ↾fun z => Sigma.desc (fun x =>
      (a.app (Opposite.op (F.elementsMk k.unop x))).app n z)
    naturality n m g := by
      ext z
      change Sigma.desc (fun x =>
        (a.app (Opposite.op (F.elementsMk k.unop x))).app m ((W.obj k).map g z)) =
        ((frames F B).obj k.unop).map g.unop ≫ Sigma.desc (fun x =>
          (a.app (Opposite.op (F.elementsMk k.unop x))).app n z)
      apply Sigma.hom_ext
      intro x
      have h := ConcreteCategory.congr_hom
        ((a.app (Opposite.op (F.elementsMk k.unop x))).naturality g) z
      change (a.app (Opposite.op (F.elementsMk k.unop x))).app m ((W.obj k).map g z) =
        (B.obj k.unop).map g.unop ≫
          (a.app (Opposite.op (F.elementsMk k.unop x))).app n z at h
      simpa [frames, diagram, Category.assoc] using h }
  naturality k l f := by
    ext n z
    change Sigma.desc (fun x =>
      (a.app (Opposite.op (F.elementsMk l.unop x))).app n ((W.map f).app n z)) =
      ((frames F B).map f.unop).app n.unop ≫ Sigma.desc (fun x =>
        (a.app (Opposite.op (F.elementsMk k.unop x))).app n z)
    apply Sigma.hom_ext
    intro x
    have h := ConcreteCategory.congr_hom (congr_app (a.naturality
      (show F.elementsMk l.unop x ⟶ F.elementsMk k.unop (F.map f.unop x) from
        { hom := f.unop, map_val := rfl }).op) n) z
    change (a.app (Opposite.op (F.elementsMk l.unop x))).app n ((W.map f).app n z) =
      (B.map f.unop).app n.unop ≫
        (a.app (Opposite.op (F.elementsMk k.unop (F.map f.unop x)))).app n z at h
    simpa [frames, diagram, Category.assoc] using h

/-- 制限と余積への再構成は、全単体・全添字で互いに逆。 -/
def weightedHomEquiv :
    (W ⟶ (FrameWeightRealization.hom K (frames F B)).obj Y) ≃
      ((Functor.Elements.π F).op ⋙ W ⟶
        (FrameWeightRealization.hom F.Elements (Functor.Elements.π F ⋙ B)).obj Y) where
  toFun := weightedHomToElements F B W Y
  invFun := weightedHomFromElements F B W Y
  left_inv a := by
    ext k n z
    apply Sigma.hom_ext
    intro x
    change Sigma.ι _ x ≫ Sigma.desc (fun x =>
      Sigma.ι _ x ≫ (a.app k).app n z) = Sigma.ι _ x ≫ (a.app k).app n z
    simp
  right_inv a := by
    ext e n z
    change Sigma.ι _ e.unop.val ≫ Sigma.desc (fun x =>
      (a.app (Opposite.op (F.elementsMk e.unop.obj x))).app n z) = (a.app e).app n z
    simp

end SerrePositivity.DiagramModel.ElementsCopower
