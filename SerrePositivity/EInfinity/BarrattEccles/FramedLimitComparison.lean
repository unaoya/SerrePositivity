module

public import SerrePositivity.EInfinity.BarrattEccles.FramedLimit

/-!
# 通常の錐から cofibrant 重みの右 frame の end への比較

概要：Hovey §5.4 の計算対象へ、元の図式の通常の錐から実際の射を構成する。
方針：右 frame の比較を錐の全射影へ合成し、重み付き Hom の普遍性を使う。
規約：図式の射・全単体作用素に厳密に自然な族を使う。
使われ方：一般極限から右導来極限への比較の構成。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity.BarrattEccles

open CategoryTheory Limits Opposite
open SerrePositivity.DiagramModel

variable (A : Type u) [CommRing A]

/-- 概要：右 frame の反対圏での augmentation（Hovey §5.2）。
方針：関手的右 frame の比較を指定した対象で評価する。
規約：全単体作用素に自然な同じ比較を使う。
使われ方：通常の錐を重み付き錐へ移す。 -/
def rightFrameAugmentation (X : (operad A).Algebra) :
    rightFrame A X ⟶ (Functor.const SimplexCategory).obj (op X) := by
  let := modelCategory A
  exact (rightFrameFamily A).augmentation.app (op X)

variable (K : Type u) [SmallCategory K]

/-- 概要：通常の錐は任意の重みに対する右 frame の錐を与える（Hovey §5.4）。
方針：各重みの単体を、元の射影と frame の比較の合成へ送る。
規約：図式全体・全単体作用素で自然、重みの単体には依存しない。
使われ方：実際の重み付き end への普遍射を構成する。 -/
def strictConeWeightedFamily (F : K ⥤ (operad A).Algebra) (W : K ⥤ SSet.{u})
    (c : Cone F) :
    (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.doubleOpWeights K).obj W ⟶
      (FrameWeightRealization.hom Kᵒᵖ (rightFrameDiagram A K F)).obj (op c.pt) where
  app k :=
    { app n := ↾fun _ =>
        (rightFrameAugmentation A (F.obj k.unop.unop)).app n.unop ≫
          (c.π.app k.unop.unop).op
      naturality {n m} θ := by
        apply ConcreteCategory.hom_ext
        intro x
        change (rightFrameAugmentation A (F.obj k.unop.unop)).app m.unop ≫
            (c.π.app k.unop.unop).op =
          (rightFrame A (F.obj k.unop.unop)).map θ.unop ≫
            (rightFrameAugmentation A (F.obj k.unop.unop)).app n.unop ≫
              (c.π.app k.unop.unop).op
        have hn := (rightFrameAugmentation A (F.obj k.unop.unop)).naturality θ.unop
        change _ ≫ _ = _ ≫ 𝟙 (op (F.obj k.unop.unop)) at hn
        rw [Category.comp_id] at hn
        simpa only [Category.assoc] using
          congrArg (fun t => t ≫ (c.π.app k.unop.unop).op) hn.symm }
  naturality {k l} f := by
    let := modelCategory A
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro x
    change (rightFrameAugmentation A (F.obj l.unop.unop)).app n.unop ≫
        (c.π.app l.unop.unop).op =
      (((rightFrameFamily A).obj.map (F.map f.unop.unop).op).app n.unop) ≫
        (rightFrameAugmentation A (F.obj k.unop.unop)).app n.unop ≫
          (c.π.app k.unop.unop).op
    have hq := congr_app ((rightFrameFamily A).augmentation.naturality
      (F.map f.unop.unop).op) n.unop
    change _ ≫ (rightFrameAugmentation A (F.obj k.unop.unop)).app n.unop =
      (rightFrameAugmentation A (F.obj l.unop.unop)).app n.unop ≫
        (F.map f.unop.unop).op at hq
    rw [← Category.assoc, hq, Category.assoc]
    change _ ≫ (c.π.app l.unop.unop).op =
      _ ≫ (c.π.app k.unop.unop ≫ F.map f.unop.unop).op
    rw [c.w]

/-- 概要：通常の錐の頂点から選んだ重みの計算対象への射（Hovey §5.4）。
方針：通常の錐から作った全単体の族を重み付き Hom の普遍性へ戻す。
規約：元の図式と選んだ同じ重み・右 frame を使う。
使われ方：通常の極限から homotopy 極限の候補への比較。 -/
def coneToFramedLimit (F : K ⥤ (operad A).Algebra) (c : Cone F) :
    c.pt ⟶ (framedLimitFunctor A K).obj F :=
  (weightedCotensorHomEquiv A K F (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.weight K) c.pt).symm
    (strictConeWeightedFamily A K F (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.weight K) c)

/-- 概要：重み付き Hom の同値は始域の射に自然（Hovey §5.4）。
方針：反対圏での実現の随伴の Hom の自然性を使う。
規約：余テンソルへの前合成を Hom 図式の後合成へ移す。
使われ方：通常の錐からの比較の頂点に関する自然性。 -/
lemma weightedCotensorHomEquiv_precomp (F : K ⥤ (operad A).Algebra)
    (W : K ⥤ SSet.{u}) {Y Z : (operad A).Algebra} (g : Z ⟶ Y)
    (h : Y ⟶ (weightedCotensor A K F).obj (op W)) :
    weightedCotensorHomEquiv A K F W Z (g ≫ h) =
      weightedCotensorHomEquiv A K F W Y h ≫
        (FrameWeightRealization.hom Kᵒᵖ (rightFrameDiagram A K F)).map g.op := by
  let adj := FrameWeightRealization.adjunction Kᵒᵖ (rightFrameDiagram A K F)
  exact adj.homEquiv_naturality_right h.op g.op

/-- 概要：通常の錐からの比較は錐の頂点の射に自然（Hovey §5.4）。
方針：重み付き Hom の始域自然性と元の錐の三角形を使う。
規約：元の同じ図式に対する通常の錐の射を使う。
使われ方：極限からの比較と任意の錐からの比較を接続する。 -/
lemma coneToFramedLimit_naturality (F : K ⥤ (operad A).Algebra)
    {c d : Cone F} (f : c ⟶ d) :
    f.hom ≫ coneToFramedLimit A K F d = coneToFramedLimit A K F c := by
  apply (weightedCotensorHomEquiv A K F (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.weight K) c.pt).injective
  rw [weightedCotensorHomEquiv_precomp]
  simp only [coneToFramedLimit, Equiv.apply_symm_apply]
  apply NatTrans.ext
  funext k
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro x
  change ((rightFrameAugmentation A (F.obj k.unop.unop)).app n.unop ≫
      (d.π.app k.unop.unop).op) ≫ f.hom.op =
    (rightFrameAugmentation A (F.obj k.unop.unop)).app n.unop ≫ (c.π.app k.unop.unop).op
  rw [Category.assoc]
  change _ ≫ (f.hom ≫ d.π.app k.unop.unop).op = _
  rw [f.w]

/-- 概要：通常の極限から cofibrant 重みの右 frame の end への比較（Hovey §5.4）。
方針：通常の極限錐からの比較を使う。
規約：この射の構成だけで右導来極限の普遍性を仮定しない。
使われ方：一般 homotopy 極限の導来比較の成分。 -/
def limitComparison (F : K ⥤ (operad A).Algebra) :
    limit F ⟶ (framedLimitFunctor A K).obj F :=
  coneToFramedLimit A K F (limit.cone F)

end SerrePositivity.EInfinity.BarrattEccles
