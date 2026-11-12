module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.FullHomotopyLift
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Quasicategory
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.HomotopyEvaluationClass

/-! # 充満 dg 包含に沿う図式の h の射の持ち上げ

概要：両端の図式が充満 dg 部分圏に入れば、周囲の関手圏の h の射も持ち上がる。
方針：射をホモトピーで代表し、円柱を持ち上げて curry し直す。
規約：任意の単体的形状。端点表示は Arrow で保持。使われ方：D7 の cofiber 比較の Semifree への反映。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory MonoidalCategory MonoidalClosed DifferentialGraded SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] (P : D → Prop)

/-- 周囲の図式関手圏の h の射を、充満部分 dg 圏の図式間の射へ持ち上げる。 -/
lemma exists_fullInclusion_functorHom {K : SSet.{max u v}}
    (f g : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (DGFullSubcategory D P))
    (a : (SSet.HomotopyCategory.mk
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgFullSubcategoryInclusion R D P))) :
        hoFunctor.obj ((ihom K).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R D))) ⟶
      SSet.HomotopyCategory.mk
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (g ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgFullSubcategoryInclusion R D P)))) :
    ∃ b : (SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f) :
        hoFunctor.obj ((ihom K).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (DGFullSubcategory D P)))) ⟶
        SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex g),
      Arrow.mk ((hoFunctor.map ((ihom K).map
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgFullSubcategoryInclusion R D P)))).toFunctor.map b) = Arrow.mk a := by
  obtain ⟨e, he⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.homotopyCategory_homMk_surjective _ _ a
  obtain ⟨H, hH⟩ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.exists_fullInclusion_homotopy R D P f g (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyOfFunctorEdge e)
  refine ⟨SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H), ?_⟩
  calc
    _ = Arrow.mk (SSet.Truncated.HomotopyCategory.homMk e) := by
      apply SSet.Truncated.HomotopyCategory.congr_arrowMk_homMk
      change ((ihom K).map (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgFullSubcategoryInclusion R D P))).app _
        (SSet.yonedaEquiv (curry H.h)) = e.edge
      rw [← SSet.yonedaEquiv_comp, ← curry_natural_right, hH]
      change SSet.yonedaEquiv (curry (uncurry (SSet.yonedaEquiv.symm e.edge))) = e.edge
      rw [curry_uncurry, Equiv.apply_symm_apply]
    _ = _ := congrArg Arrow.mk he

end SerrePositivity.InfinityCategories.Project.DerivedCategories
