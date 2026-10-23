module

public import SerrePositivity.InfinityCategories.F2.Presentable.SimplicialHomEnriched
public import SerrePositivity.InfinityCategories.F2.FiniteInternalHomContinuity
public import SerrePositivity.InfinityCategories.F2.Ind.StrictCoconePostcomposition
public import SerrePositivity.InfinityCategories.F2.Ind.FilteredKanCocone
public import SerrePositivity.InfinityCategories.F2.Ind.CoconeTransformationPointPost
public import SerrePositivity.InfinityCategories.F2.CoconeValEquality

/-!
概要：有限単体集合始点の全 Hom が、同じ strict filtered 余極限余錐を native に保存する。
方針：全豊穣作用の通常の作用を照合し、既存の有限内部 Hom の連続性を指定余錐像へ渡す。
規約：始点の Kan 性は要求しない。元の全脚と全単体を保持する。
使われ方：一般 coherent 図式での有限始点の filtered 保存。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.F2.Presentable
open HomotopyLimits

/-- 全豊穣内部 Hom の通常の作用は、元の strict 内部 Hom 関手そのもの。 -/
lemma simplicialInternalHomEnriched_underlying (K : SSet.{u}) :
    coherentEnrichedUnderlyingFunctor (simplicialInternalHomEnriched K) =
      simplicialInternalHomFunctor K := by
  refine CategoryTheory.Functor.ext
    (F := coherentEnrichedUnderlyingFunctor (simplicialInternalHomEnriched K))
    (G := simplicialInternalHomFunctor K) (fun _ ↦ rfl) ?_
  intro L M f
  change (coherentEnrichedUnderlyingFunctor (simplicialInternalHomEnriched K)).map f =
    (simplicialInternalHomFunctor K).map f
  apply (SimplicialCategory.homEquiv'
    ((simplicialInternalHomEnriched K).obj L) ((simplicialInternalHomEnriched K).obj M)).injective
  rw [coherentEnrichedUnderlyingFunctor_vertex]
  have ht : MonoidalClosed.curry' (C := SSet.{u}) f ≫
      MonoidalClosed.curry (MonoidalClosed.comp K L.obj M.obj) =
      MonoidalClosed.curry' ((ihom K).map f) := by
    apply MonoidalClosed.uncurry_injective
    rw [MonoidalClosed.uncurry_natural_left, MonoidalClosed.uncurry_curry]
    simp only [MonoidalClosed.curry', MonoidalClosed.uncurry_curry]
    exact MonoidalClosed.whiskerLeft_curry'_comp (C := SSet.{u}) f
  have hp := congrArg (fun q : (𝟙_ SSet.{u}) ⟶
      (ihom ((ihom K).obj L.obj)).obj
        ((ihom K).obj M.obj) ↦ SSet.unitHomEquiv _ q) ht
  exact hp

/-- 同じ全余錐への Hom 後合成は、元の通常の Hom 余錐の全単体と一致する。 -/
lemma simplicialInternalHom_strictCocone_postcomp_val (K : SSet.{u})
    {J : Type u} [SmallCategory J] {F : J ⥤ KanObject.{u}} (c : Cocone F) :
    (strictNativeCocone c).val ≫ simplicialInternalHomInfinity K =
      (strictNativeCocone ((simplicialInternalHomFunctor K).mapCocone c)).val := by
  rw [simplicialInternalHomInfinity, Ind.strictNativeCocone_postcomp_val,
    simplicialInternalHomEnriched_underlying]

/-- 有限始点からの全 Hom の像は、同じ filtered strict 全余錐の native な余極限である。 -/
lemma finiteSimplicialHomInfinity_preserves_strictCocone (K : SSet.{u}) [K.Finite]
    {J : Type u} [SmallCategory J] [IsFiltered J] {F : J ⥤ KanObject.{u}}
    (c : Cocone F) (hc : IsColimit (kanObjectForget.mapCocone c)) :
    IsColimitCone (mapJoinCocone (simplicialInternalHomInfinity K) (strictNativeCocone c)) := by
  apply (isColimitCone_iff_of_cocone_val_eq _ _
    (simplicialInternalHom_strictCocone_postcomp_val K c)).mpr
  apply Ind.strictNativeCocone_isColimit_of_filtered_forget
  exact isColimitOfPreserves (ihom K) hc

end SerrePositivity.InfinityCategories.F2.Presentable
