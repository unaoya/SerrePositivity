module

public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.StrictDiagramFreeArrowHom

/-!
概要：自由frameの全族を元のsource frameへ増大し、そのHomを指定錐の脚と照合する。
方針：自由図式の余積の各挿入に、添字射との合成を作用させる。
規約：重みの実現後の弱同値性はまだ主張しない。
使われ方：HTT 4.2.4.4のRR02(a)、指定Bousfield–Kan比較の源の固定。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits SSet
open SerrePositivity.DifferentialGraded
open SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
variable (A : Type u) [CommRing A] (d : StrictDiagramDirection)
local instance : ∀ (i j : strictDiagramIndex d),
    HasCoproductsOfShape (i ⟶ j) (Complex A) :=
  fun _ _ => HomologicalComplex.instHasColimitsOfShape
local instance : HomotopicalAlgebra.ModelCategory (StrictComplexDiagram A d) :=
  strictDiagramReedyModelCategory A d

/-- 指定した添字射の自由frameから元のframeへの増大の成分。 -/
def strictDiagramFreeArrowAugmentationComponent (X : StrictComplexDiagram A d)
    (t : StrictDiagramArrowElements.{u} d) :
    (strictDiagramFreeArrowFrame A d X).obj (Opposite.op t) ⟶
      (strictDiagramSourceFrame A d X).obj where
  app n :=
    { app := fun k => Sigma.desc (fun h =>
        ((strictDiagramSourceFrame A d X).obj.obj n).map (AsSmall.down.map t.val ≫ h))
      naturality := by
        intro k l a
        apply Sigma.hom_ext
        intro h
        simp [strictDiagramFreeArrowFrame, strictDiagramFreeArrowIndex,
          strictDiagramFreeValueFrameFamily, strictDiagramFreeAtFunctor,
          strictDiagramFreeAt, strictDiagramEvaluatedSourceFrames,
          Category.assoc, ← CategoryTheory.Functor.map_comp] }
  naturality := by
    intro m n a
    apply NatTrans.ext
    funext k
    apply Sigma.hom_ext
    intro h
    simpa [strictDiagramFreeArrowFrame, strictDiagramFreeArrowIndex,
      strictDiagramFreeValueFrameFamily, strictDiagramFreeAtFunctor,
      strictDiagramFreeAt, strictDiagramEvaluatedSourceFrames, Category.assoc] using
      (((strictDiagramSourceFrame A d X).obj.map a).naturality
        (AsSmall.down.map t.val ≫ h)).symm

/-- 全添字射に自然な、元のsource frameへの増大射。 -/
def strictDiagramFreeArrowAugmentation (X : StrictComplexDiagram A d) :
    strictDiagramFreeArrowFrame A d X ⟶
      (Functor.const (StrictDiagramArrowElements.{u} d)ᵒᵖ).obj
        (strictDiagramSourceFrame A d X).obj where
  app t := strictDiagramFreeArrowAugmentationComponent A d X t.unop
  naturality := by
    intro t s g
    apply NatTrans.ext
    funext n
    apply NatTrans.ext
    funext k
    apply Sigma.hom_ext
    intro h
    have hg := g.unop.map_val
    change (g.unop.hom.1.unop ≫ s.unop.val) ≫ g.unop.hom.2 = t.unop.val at hg
    have hd := congrArg (fun f => AsSmall.down.map f) hg
    change (AsSmall.down.map g.unop.hom.1.unop ≫ AsSmall.down.map s.unop.val) ≫
      AsSmall.down.map g.unop.hom.2 = AsSmall.down.map t.unop.val at hd
    simp [strictDiagramFreeArrowAugmentationComponent, strictDiagramFreeArrowFrame,
      strictDiagramFreeArrowIndex, strictDiagramFreeValueFrameFamily, strictDiagramFreeAtFunctor,
      strictDiagramFreeAtReindex, strictDiagramFreeAt, strictDiagramEvaluatedSourceFrames,
      Category.assoc, ← CategoryTheory.Functor.map_comp]
    have hh := congrArg (fun a => ((strictDiagramSourceFrame A d X).obj.obj n).map (a ≫ h)) hd
    simp only [Category.assoc] at hh
    convert hh using 1 <;> rfl

/-- 同じ増大射のHomは、既に指定した全frame Homの錐の脚に一致する。 -/
lemma strictDiagramFreeArrowAugmentation_hom (X Y : StrictComplexDiagram A d)
    (t : StrictDiagramArrowElements.{u} d) :
    (CosimplicialHom.cosimplicialHomMap
      ((strictDiagramFreeArrowAugmentation A d X).app (Opposite.op t))).app
        (strictDiagramFibrantTarget A d Y) ≫
      (strictDiagramFreeArrowHomIso A d X Y t).hom =
        strictDiagramFrameArrowLeg A d X Y t := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro f
  change Sigma.ι (fun _ : AsSmall.down.obj t.obj.2 ⟶ AsSmall.down.obj t.obj.2 =>
      ((strictDiagramSourceFrame A d X).obj.obj n.unop).obj (AsSmall.down.obj t.obj.1.unop))
      (𝟙 _) ≫
      (((strictDiagramFreeArrowAugmentationComponent A d X t).app n.unop).app
        (AsSmall.down.obj t.obj.2) ≫ f.app (AsSmall.down.obj t.obj.2)) =
    ((strictDiagramSourceFrame A d X).obj.obj n.unop).map (AsSmall.down.map t.val) ≫
      f.app (AsSmall.down.obj t.obj.2)
  dsimp only [strictDiagramFreeArrowAugmentationComponent]
  rw [Sigma.ι_comp_desc_assoc]
  simp only [Category.comp_id]

end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
