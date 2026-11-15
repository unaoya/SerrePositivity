module

public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.StrictDiagramFreeArrowAugmentation
public import Mathlib.CategoryTheory.Comma.Over.Basic

/-!
概要：自由図式を一つの頂点で評価した余積の添字圏と、合成によるOver圏への比較。
方針：余積の添字をHom要素圏上の要素圏として表し、二本の射を合成する。
規約：この比較のhomotopy final性・実現後の弱同値性はここでは主張しない。
使われ方：HTT 4.2.4.4のRR02(a)、実増大射の評価点での比較。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison

/-- 評価点kでの自由図式の余積の添字を与える、同じHom関手。 -/
def strictDiagramFreeEvaluationWeight (d : StrictDiagramDirection) (k : strictDiagramIndex d) :
    (StrictDiagramArrowElements.{u} d)ᵒᵖ ⥤ Type :=
  strictDiagramFreeArrowIndex d ⋙ CategoryTheory.Prod.fst _ _ ⋙ yoneda.obj k

/-- 二本の射 i → j → k を対象とする、実余積の添字圏。 -/
abbrev StrictDiagramFreeEvaluationIndex (d : StrictDiagramDirection) (k : strictDiagramIndex d) :=
  (strictDiagramFreeEvaluationWeight.{u} d k).Elements

/-- 二本の射を合成し、指定評価点のOver圏へ送る。 -/
def strictDiagramFreeEvaluationToOver (d : StrictDiagramDirection) (k : strictDiagramIndex d) :
    StrictDiagramFreeEvaluationIndex.{u} d k ⥤ Over k where
  obj t := Over.mk (AsSmall.down.map t.obj.unop.val ≫ t.val)
  map {t s} g := Over.homMk (AsSmall.down.map g.hom.unop.hom.1.unop) (by
    have ht := g.hom.unop.map_val
    change (g.hom.unop.hom.1.unop ≫ s.obj.unop.val) ≫ g.hom.unop.hom.2 = t.obj.unop.val at ht
    have hd := congrArg (fun a => AsSmall.down.map a) ht
    change (AsSmall.down.map g.hom.unop.hom.1.unop ≫ AsSmall.down.map s.obj.unop.val) ≫
      AsSmall.down.map g.hom.unop.hom.2 = AsSmall.down.map t.obj.unop.val at hd
    have hv := g.map_val
    change AsSmall.down.map g.hom.unop.hom.2 ≫ t.val = s.val at hv
    change AsSmall.down.map g.hom.unop.hom.1.unop ≫
      (AsSmall.down.map s.obj.unop.val ≫ s.val) = AsSmall.down.map t.obj.unop.val ≫ t.val
    rw [← hv]
    simpa only [Category.assoc] using congrArg (fun a => a ≫ t.val) hd)
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Over圏の射に恒等射を付けた、同じ添字圏の対象。 -/
def strictDiagramFreeEvaluationSectionObj (d : StrictDiagramDirection) (k : strictDiagramIndex d)
    (t : Over k) : StrictDiagramFreeEvaluationIndex.{u} d k :=
  { obj := Opposite.op
      { obj := (Opposite.op (AsSmall.up.obj t.left), AsSmall.up.obj k)
        val := AsSmall.up.map t.hom }
    val := 𝟙 k }

/-- Over圏の全射を、同じ恒等射付きの添字間の射へ送る。 -/
def strictDiagramFreeEvaluationSection (d : StrictDiagramDirection) (k : strictDiagramIndex d) :
    Over k ⥤ StrictDiagramFreeEvaluationIndex.{u} d k where
  obj := strictDiagramFreeEvaluationSectionObj d k
  map {t s} f :=
    { hom := Quiver.Hom.op
        { hom := ((AsSmall.up.map f.left).op, 𝟙 _)
          map_val := by
            change (AsSmall.up.map f.left ≫ AsSmall.up.map s.hom) ≫ 𝟙 _ = AsSmall.up.map t.hom
            simp only [Category.comp_id, ← CategoryTheory.Functor.map_comp, Over.w] }
      map_val := by change 𝟙 k ≫ 𝟙 k = 𝟙 k; simp }
  map_id _ := rfl
  map_comp f g := by
    apply Functor.Elements.Hom.ext
    apply Quiver.Hom.unop_inj
    apply Functor.Elements.Hom.ext
    apply Prod.ext
    · rfl
    · exact (Category.id_comp _).symm

end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
