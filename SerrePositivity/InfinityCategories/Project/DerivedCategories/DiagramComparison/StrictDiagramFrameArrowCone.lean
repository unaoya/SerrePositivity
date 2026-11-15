module

public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.StrictDiagramFrameEndCoefficients
public import Mathlib.CategoryTheory.Elements
public import Mathlib.CategoryTheory.Yoneda

/-!
概要：元のframeの自然変換を、Homの要素圏上の全単体的な錐へ送る。
方針：各添字の射へframeの作用を前合成し、全ての可換な分解に対する自然性を使う。
規約：この錐の導来極限性はまだ主張しない。
使われ方：HTT 4.2.4.4のRR02(a)、twisted-arrow上の実比較の構成。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits SSet
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison

/-- 元の添字のHomの要素圏。対象は実際の添字射、射はその前後合成の分解。 -/
abbrev StrictDiagramArrowElements (d : StrictDiagramDirection) :=
  (Functor.uncurry.obj (coyoneda (C := AsSmall.{u} (strictDiagramIndex d)))).Elements

/-- 同じ添字射の始点と終点を、既存の二変数係数の底へ送る。 -/
def strictDiagramArrowElementsBase (d : StrictDiagramDirection) :
    StrictDiagramArrowElements.{u} d ⥤
      AsSmall.{u} ((strictDiagramIndex d)ᵒᵖ × strictDiagramIndex d) :=
  Functor.Elements.π _ ⋙ CategoryTheory.Prod.swap _ _ ⋙ strictDiagramEndIndexFunctor d

variable (A : Type u) [CommRing A] (d : StrictDiagramDirection)
  (X Y : StrictComplexDiagram A d)
local instance arrowConeModel : HomotopicalAlgebra.ModelCategory (StrictComplexDiagram A d) :=
  strictDiagramReedyModelCategory A d

/-- 実際の添字射で評価した、同じframeの二変数係数。 -/
def strictDiagramFrameArrowDiagram : StrictDiagramArrowElements.{u} d ⥤ SSet.{u} :=
  strictDiagramArrowElementsBase d ⋙ strictDiagramEvaluatedValueKan A d X Y ⋙ kanObjectForget

/-- 元の全自然変換を、指定した添字射に沿うHomへ送る実写像。 -/
def strictDiagramFrameArrowLeg (t : StrictDiagramArrowElements.{u} d) :
    strictDiagramFrameMapping A d X Y ⟶ (strictDiagramFrameArrowDiagram A d X Y).obj t where
  app n := ↾fun f =>
    ((strictDiagramSourceFrame A d X).obj.obj n.unop).map (AsSmall.down.map t.val) ≫
      f.app (AsSmall.down.obj t.obj.2)
  naturality := by
    intro n m θ
    apply ConcreteCategory.hom_ext
    intro f
    symm
    change ((strictDiagramSourceFrame A d X).obj.map θ.unop).app _ ≫
        (((strictDiagramSourceFrame A d X).obj.obj n.unop).map (AsSmall.down.map t.val) ≫
          f.app _) =
      ((strictDiagramSourceFrame A d X).obj.obj m.unop).map (AsSmall.down.map t.val) ≫
        (((strictDiagramSourceFrame A d X).obj.map θ.unop).app _ ≫ f.app _)
    rw [← Category.assoc, ← ((strictDiagramSourceFrame A d X).obj.map θ.unop).naturality,
      Category.assoc]

/-- 全ての前後合成の分解に対し、同じframeの成分は錐の自然性を満たす。 -/
lemma strictDiagramFrameArrowLeg_naturality {t s : StrictDiagramArrowElements.{u} d}
    (g : t ⟶ s) :
    strictDiagramFrameArrowLeg A d X Y t ≫ (strictDiagramFrameArrowDiagram A d X Y).map g =
      strictDiagramFrameArrowLeg A d X Y s := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro f
  have hg : g.hom.1.unop ≫ t.val ≫ g.hom.2 = s.val := by
    have h := g.map_val
    change (g.hom.1.unop ≫ t.val) ≫ g.hom.2 = s.val at h
    simpa only [Category.assoc] using h
  have hh := congrArg (fun k => AsSmall.down.map k) hg
  change AsSmall.down.map g.hom.1.unop ≫ AsSmall.down.map t.val ≫
      AsSmall.down.map g.hom.2 = AsSmall.down.map s.val at hh
  change ((strictDiagramSourceFrame A d X).obj.obj n.unop).map (AsSmall.down.map g.hom.1.unop) ≫
      (((strictDiagramSourceFrame A d X).obj.obj n.unop).map (AsSmall.down.map t.val) ≫ f.app _) ≫
        (strictDiagramFibrantTarget A d Y).map (AsSmall.down.map g.hom.2) =
      ((strictDiagramSourceFrame A d X).obj.obj n.unop).map (AsSmall.down.map s.val) ≫ f.app _
  simp only [Category.assoc]
  rw [← f.naturality]
  have h := congrArg (fun k =>
    ((strictDiagramSourceFrame A d X).obj.obj n.unop).map k ≫
      f.app (AsSmall.down.obj s.obj.2)) hh
  simpa only [CategoryTheory.Functor.op_obj, Opposite.unop_op,
    CategoryTheory.Functor.map_comp, Category.assoc] using h

/-- 元の全frame Homを頂点とする、Hom要素圏上の指定錐。 -/
def strictDiagramFrameArrowCone : Cone (strictDiagramFrameArrowDiagram A d X Y) where
  pt := strictDiagramFrameMapping A d X Y
  π := { app := strictDiagramFrameArrowLeg A d X Y
         naturality := by intro t s g; simpa using (strictDiagramFrameArrowLeg_naturality A d X Y g).symm }

end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
