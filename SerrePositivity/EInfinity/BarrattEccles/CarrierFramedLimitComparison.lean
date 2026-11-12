module

public import SerrePositivity.EInfinity.BarrattEccles.CarrierFramedLimitClasses
public import SerrePositivity.EInfinity.BarrattEccles.CarrierDiagramForget
public import SerrePositivity.EInfinity.BarrattEccles.CarrierRightSimplicialFrames

/-!
# 底の通常錐から同じ右 frame の end への比較

概要：BM 命題 4.1・Hovey §5.4 の底の通常錐から実際の比較射を構成する。
方針：元の脚と忘却した augmentation の全単体の族に実現随伴を適用する。
規約：任意の複体を頂点とし、元の右 frame と底の計算同型を保持する。
使われ方：底の導来 Hom 比較を通常の錐で正規化する。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity.BarrattEccles

open CategoryTheory Limits Opposite
open SerrePositivity.DifferentialGraded
open SerrePositivity.DiagramModel

variable (A : Type u) [CommRing A] (K : Type u) [SmallCategory K]

/-- 概要：通常の錐は任意の重みに対する右 frame の錐を与える（Hovey §5.4）。
方針：各重みの単体を、元の射影と frame の比較の合成へ送る。
規約：図式全体・全単体作用素で自然、重みの単体には依存しない。
使われ方：実際の重み付き end への普遍射を構成する。 -/
def carrierStrictConeWeightedFamily (F : K ⥤ (operad A).Algebra) (W : K ⥤ SSet.{u})
    (c : Cone ((Diagram.forget A K).obj F)) :
    (SerrePositivity.EInfinity.HomotopyWeight.doubleOpWeights K).obj W ⟶
      (FrameWeightRealization.hom Kᵒᵖ (carrierRightFrameDiagram A K F)).obj (op c.pt) where
  app k :=
    { app n := ↾fun _ =>
        (carrierRightFrameAugmentation A (F.obj k.unop.unop)).app n.unop ≫
          (c.π.app k.unop.unop).op
      naturality {n m} θ := by
        apply ConcreteCategory.hom_ext
        intro x
        change (carrierRightFrameAugmentation A (F.obj k.unop.unop)).app m.unop ≫
            (c.π.app k.unop.unop).op =
          (carrierRightFrame A (F.obj k.unop.unop)).map θ.unop ≫
            (carrierRightFrameAugmentation A (F.obj k.unop.unop)).app n.unop ≫
              (c.π.app k.unop.unop).op
        have hn := (carrierRightFrameAugmentation A (F.obj k.unop.unop)).naturality θ.unop
        change _ ≫ _ = _ ≫ 𝟙 (op (F.obj k.unop.unop).carrier) at hn
        rw [Category.comp_id] at hn
        simpa only [Category.assoc] using
          congrArg (fun t => t ≫ (c.π.app k.unop.unop).op) hn.symm }
  naturality {k l} f := by
    let := modelCategory A
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro x
    change (carrierRightFrameAugmentation A (F.obj l.unop.unop)).app n.unop ≫
        (c.π.app l.unop.unop).op =
      (((carrierRightSimplicialFrameFamily A).map (F.map f.unop.unop)).app n).op ≫
        (carrierRightFrameAugmentation A (F.obj k.unop.unop)).app n.unop ≫
          (c.π.app k.unop.unop).op
    have hq := congr_app ((carrierRightSimplicialFrameAugmentation A).naturality
      (F.map f.unop.unop)) n
    have hu := congrArg Quiver.Hom.op hq.symm
    change _ ≫ (carrierRightFrameAugmentation A (F.obj k.unop.unop)).app n.unop =
      (carrierRightFrameAugmentation A (F.obj l.unop.unop)).app n.unop ≫
        (((Diagram.forget A K).obj F).map f.unop.unop).op at hu
    calc
      _ = (carrierRightFrameAugmentation A (F.obj l.unop.unop)).app n.unop ≫
          (c.π.app k.unop.unop ≫ ((Diagram.forget A K).obj F).map f.unop.unop).op :=
        congrArg (fun z =>
          (carrierRightFrameAugmentation A (F.obj l.unop.unop)).app n.unop ≫ z.op)
            (c.w f.unop.unop).symm
      _ = ((carrierRightFrameAugmentation A (F.obj l.unop.unop)).app n.unop ≫
          (((Diagram.forget A K).obj F).map f.unop.unop).op) ≫
            (c.π.app k.unop.unop).op := (Category.assoc _ _ _).symm
      _ = _ := congrArg (fun z => z ≫ (c.π.app k.unop.unop).op) hu.symm


/-- 概要：通常の錐の頂点から選んだ重みの計算対象への射（Hovey §5.4）。
方針：通常の錐から作った全単体の族を重み付き Hom の普遍性へ戻す。
規約：元の図式と選んだ同じ重み・右 frame を使う。
使われ方：通常の極限から homotopy 極限の候補への比較。 -/
def carrierConeToFramedLimit (F : K ⥤ (operad A).Algebra)
    (c : Cone ((Diagram.forget A K).obj F)) :
    c.pt ⟶ ((framedLimitFunctor A K).obj F).carrier :=
  (((FrameWeightRealization.adjunction Kᵒᵖ (carrierRightFrameDiagram A K F)).homEquiv
    (SerrePositivity.EInfinity.HomotopyWeight.framedLimitWeight K) (op c.pt)).symm
      (carrierStrictConeWeightedFamily A K F (HomotopyWeight.weight K) c)).unop ≫
    (framedLimitCarrierIso A K F).inv

end SerrePositivity.EInfinity.BarrattEccles
