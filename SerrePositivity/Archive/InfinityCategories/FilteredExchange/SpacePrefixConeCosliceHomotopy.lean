module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.SpacePrefixConeCosliceMap
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentPrefixConeOne
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentPrefixConeZero
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.SpaceSimplexSourceConeZeroFace
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorHomotopy

/-!
概要：同じ固定始点の最大化 cone から元の実 cone への coslice ホモトピー。
方針：prefix 円柱の全次数の両端を、元の zero-face 座標で同定する。
規約：実際の cone と指定精密化を保持し、比較の代表を選び直さない。
使われ方：零面の全係数比較を元の指定 path へ戻す。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
open HomotopyLimits
variable {n : ℕ} (s : SpaceInfinity.{u} _⦋n + 1⦌)
local notation "K" => EnrichedFunctor.obj s (SimplicialThickening.mk (ULift.up 0))
local notation "Z" => sliceUnder (SSet.yonedaEquiv.symm (coherentNerveVertex K))

/-- 元の cone へ至る固定始点の実 coslice ホモトピー。 -/
def spacePrefixConeCosliceHomotopy :
    SSet.Homotopy
      (SSet.yonedaEquiv.symm (SimplicialObject.δ Z 0
        (spaceSimplexSourceCone (coherentSimplexMaximalization s))))
      (SSet.yonedaEquiv.symm (SimplicialObject.δ Z 0 (spaceSimplexSourceCone s))) where
  h := spacePrefixConeCosliceMap s
  h₀ := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro a
    apply spaceCosliceSourceSimplex_injective K d.unop.len
    change coherentCosliceSourceSimplex K
      (spacePrefixConeCosliceSimplex s a.down.toOrderHom (OrderHom.const _ 0)) =
        coherentCosliceSourceSimplex K
          (CategoryTheory.Functor.map Z a.down.op (SimplicialObject.δ Z 0
            (spaceSimplexSourceCone (coherentSimplexMaximalization s))))
    refine (spacePrefixConeCosliceSimplex_coordinates s _ _).trans
      ((coherentPrefixConeSimplex_zero s _).trans ?_)
    exact (congrArg (fun z ↦ (SimplicialThickening.functor
      (prependOrderHom a.down.toOrderHom).uliftMap).comp SSet z)
        (spaceSimplexSourceCone_zero_face_coordinates
          (coherentSimplexMaximalization s))).symm.trans
            (coherentCosliceSourceSimplex_reindex K a.down _)
  h₁ := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro a
    apply spaceCosliceSourceSimplex_injective K d.unop.len
    change coherentCosliceSourceSimplex K
      (spacePrefixConeCosliceSimplex s a.down.toOrderHom (OrderHom.const _ 1)) =
        coherentCosliceSourceSimplex K (CategoryTheory.Functor.map Z a.down.op
          (SimplicialObject.δ Z 0 (spaceSimplexSourceCone s)))
    refine (spacePrefixConeCosliceSimplex_coordinates s _ _).trans
      ((coherentPrefixConeSimplex_one s _).trans ?_)
    exact (congrArg (fun z ↦ (SimplicialThickening.functor
      (prependOrderHom a.down.toOrderHom).uliftMap).comp SSet z)
        (spaceSimplexSourceCone_zero_face_coordinates s)).symm.trans
          (coherentCosliceSourceSimplex_reindex K a.down _)
  rel := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro x
    exact False.elim x.1.property

end SerrePositivity.InfinityCategories.F2
