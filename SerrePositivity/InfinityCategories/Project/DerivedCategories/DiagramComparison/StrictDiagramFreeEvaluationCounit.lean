module

public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.StrictDiagramFreeEvaluationIndex

/-!
概要：評価点の添字圏をOver圏へ合成して戻す比較の余単位。
方針：元の二本目の射を使い、恒等射付きの添字から元の添字へ送る。
規約：全対象と全射で自然な比較を作る。実現の弱同値性はまだ主張しない。
使われ方：HTT 4.2.4.4のRR02(a)、評価点の添字比較の随伴への入力。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
variable (d : StrictDiagramDirection) (k : strictDiagramIndex d)

/-- 合成した射に恒等射を付けた添字から、元の添字へ戻す実射。 -/
def strictDiagramFreeEvaluationCounitComponent (t : StrictDiagramFreeEvaluationIndex.{u} d k) :
    (strictDiagramFreeEvaluationSection d k).obj ((strictDiagramFreeEvaluationToOver d k).obj t) ⟶ t where
  hom := Quiver.Hom.op
    { hom := (𝟙 _, AsSmall.up.map t.val)
      map_val := by
        change (𝟙 _ ≫ t.obj.unop.val) ≫ AsSmall.up.map t.val =
          AsSmall.up.map (AsSmall.down.map t.obj.unop.val ≫ t.val)
        simp only [Category.id_comp, CategoryTheory.Functor.map_comp]
        rfl }
  map_val := by change t.val ≫ 𝟙 k = t.val; exact Category.comp_id _

/-- 合成して戻す比較は、余積の添字圏の全射に自然。 -/
def strictDiagramFreeEvaluationCounit :
    strictDiagramFreeEvaluationToOver.{u} d k ⋙ strictDiagramFreeEvaluationSection d k ⟶
      𝟭 (StrictDiagramFreeEvaluationIndex.{u} d k) where
  app := strictDiagramFreeEvaluationCounitComponent d k
  naturality := by
    intro t s g
    apply Functor.Elements.Hom.ext
    apply Quiver.Hom.unop_inj
    apply Functor.Elements.Hom.ext
    apply Prod.ext
    · simp [strictDiagramFreeEvaluationCounitComponent,
        strictDiagramFreeEvaluationToOver, strictDiagramFreeEvaluationSection]
      rfl
    · have h := g.map_val
      change AsSmall.down.map g.hom.unop.hom.2 ≫ t.val = s.val at h
      change (AsSmall.up.map s.val) ≫ 𝟙 _ = g.hom.unop.hom.2 ≫ AsSmall.up.map t.val
      rw [Category.comp_id]
      have hh := congrArg (fun a => AsSmall.up.map a) h
      simp only [CategoryTheory.Functor.map_comp] at hh
      convert hh.symm using 1 <;> rfl

end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
