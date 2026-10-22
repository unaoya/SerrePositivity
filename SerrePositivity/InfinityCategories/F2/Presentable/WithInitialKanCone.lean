module

public import SerrePositivity.InfinityCategories.F2.Presentable.ThinConeIndexComparison
public import SerrePositivity.InfinityCategories.HomotopyLimits.KanConeLimits
public import SerrePositivity.InfinityCategories.F2.LimitConeFamilyReadback

/-!
概要：WithInitial 上の Kan 図式の元の錐と、錐形状による同じ図式の実現を照合する。
方針：thin な添字での全単体の等式を、元の Kan 図式へ後合成する。
規約：Kan 図式自身に thin 性を要求しない。元の全脚を保持する。
使われ方：共同 strictification の各段階を N の実際の極限錐へ接続する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable
open HomotopyLimits
variable {I : Type u} [SmallCategory I] (G : WithInitial I ⥤ KanObject.{u})

/-- 始対象からの元の射を脚に持つ、同じ制限図式の Kan 値の錐。 -/
def withInitialKanCone : Cone (WithInitial.incl ⋙ G) where
  pt := G.obj WithInitial.star
  π := (WithInitial.mkCommaObject G).hom

/-- 錐添字の宇宙を調整しても、元の頂点と脚の拡張関手そのものを回収する。 -/
lemma withInitialKanCone_strictFunctor :
    coneIndexResize I ⋙ AsSmall.down ⋙ G = strictConeFunctor (withInitialKanCone G) := by
  refine CategoryTheory.Functor.ext (fun x ↦ by cases x <;> rfl) ?_
  rintro (x | _) (y | _) f
  · rfl
  · exact PEmpty.elim (show PEmpty from f)
  · simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    congr 1
    rfl
  · simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    change G.map (𝟙 WithInitial.star) = 𝟙 _
    exact G.map_id _

/-- thin な添字では、元の錐形状上の実現は N の strict な coherent 錐と全単体で一致する。 -/
lemma withInitialKanCone_coherentMap [Quiver.IsThin I] :
    (uliftInitialConeIso I).inv ≫ kanDiagramCoherentNerve G =
      strictCoherentConeMap (withInitialKanCone G) := by
  rw [← strictCoherentDiagram_eq_kanDiagram]
  unfold strictCoherentDiagram strictCoherentConeMap
  rw [← Category.assoc (uliftInitialConeIso I).inv, ← thinConeIndex_comparison I]
  simp only [Category.assoc]
  erw [← Category.assoc (nerveMap (coneIndexResize I)), resizedNerveMap_precomp,
    withInitialKanCone_strictFunctor]

/-- 同じ錐形状で実現した図式の極限性は、読み戻した N の実際の錐の極限性と同値。 -/
lemma withInitialKanCone_isLimit_iff [Quiver.IsThin I] :
    IsLimitCone (functorVertexCone (functorVertex
      ((uliftInitialConeIso I).inv ≫ kanDiagramCoherentNerve G))) ↔
      IsLimitCone (strictCoherentCone (withInitialKanCone G)) := by
  rw [withInitialKanCone_coherentMap]
  exact isLimitCone_functorVertexCone_functorVertex (strictCoherentCone (withInitialKanCone G))

end SerrePositivity.InfinityCategories.F2.Presentable
