module

public import SerrePositivity.InfinityCategories.F2.Presentable.FilteredComparisonContinuity
public import SerrePositivity.InfinityCategories.HomotopyLimits.Presentable.WithInitialKanCone
public import SerrePositivity.InfinityCategories.F2.Presentable.KanFamilyColimit

/-!
概要：WithInitial の共同 Kan 図式の各段階の native 極限性は、同じ関手圏の μ-filtered 余極限へ移る。
方針：元の錐の比較射を二つの連続関手間の自然変換にし、その余極限成分の弱同値性を検証する。
規約：頂点・図式・全脚は元の strict 余極限図式そのもの。
使われ方：coherent な錐族の模型の極限性を、元の指定された点ごとの余極限余錐へ戻す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.F2.Presentable
open HomotopyLimits
variable (I : Type u) [SmallCategory I]

/-- 元の WithInitial の単体集合値図式から、同じ頂点・脚の錐を読む。 -/
def withInitialSSetCone (H : WithInitial I ⥤ SSet.{u}) : Cone (WithInitial.incl ⋙ H) where
  pt := H.obj WithInitial.star
  π := (WithInitial.mkCommaObject H).hom

/-- 元の錐の比較射は、始対象評価と同じ Bousfield–Kan 模型との間の一つの自然変換。 -/
def withInitialConeComparison :
    (evaluation (WithInitial I) SSet.{u}).obj WithInitial.star ⟶
      (Functor.whiskeringLeft I (WithInitial I) SSet.{u}).obj WithInitial.incl ⋙
        bousfieldKanHolimFunctor I where
  app H := bousfieldKanConeComparison (withInitialSSetCone I H)
  naturality H H' η := weightedConeComparison_naturality (bousfieldKanWeight I)
    (withInitialSSetCone I H) (withInitialSSetCone I H') (η.app WithInitial.star)
    (Functor.whiskerLeft WithInitial.incl η)
    (fun i ↦ (η.naturality (WithInitial.starInitial.to (WithInitial.of i))).symm)

variable {κ μ : Cardinal.{u}} [Fact κ.IsRegular] [Fact μ.IsRegular]

/-- 元の比較の標的関手は、小さい poset 上で μ-filtered 余極限を保つ。 -/
lemma withInitialComparisonTarget_preservesCardinalFilteredColimits
    (h : IsCardinalChangeBound κ μ) (I : Type u) [PartialOrder I] (hI : HasCardinalLT I μ)
    (J : Type u) [SmallCategory J] [IsCardinalFiltered J μ] :
    PreservesColimitsOfShape J
      ((Functor.whiskeringLeft I (WithInitial I) SSet.{u}).obj WithInitial.incl ⋙
        bousfieldKanHolimFunctor I) := by
  have := bousfieldKanHolimFunctor_poset_preservesCardinalFilteredColimits h I hI J
  infer_instance

/-- 元の共同 WithInitial 図式の strict 余極限の錐自身が native な極限錐。 -/
lemma withInitialFilteredColimit_isLimit
    (h : IsCardinalChangeBound κ μ) (I : Type u) [PartialOrder I] (hI : HasCardinalLT I μ)
    (J : Type u) [SmallCategory J] [IsCardinalFiltered J μ]
    (F : J ⥤ WithInitial I ⥤ KanObject.{u})
    (hc : ∀ j, IsLimitCone (strictCoherentCone (withInitialKanCone (F.obj j)))) :
    letI := isFiltered_of_isCardinalFiltered J μ
    IsLimitCone (strictCoherentCone (withInitialKanCone (cardinalFilteredKanDiagram F))) := by
  have := isFiltered_of_isCardinalFiltered J μ
  apply kanCone_isLimit_of_bousfieldKanComparison
  change IsWeakHomotopyEquivalence
    ((withInitialConeComparison I).app (colimit (kanConeFamilyUnderlying F)))
  apply comparison_colimit_isWeakHomotopyEquivalence
    (withInitialConeComparison I) (kanConeFamilyUnderlying F) (by infer_instance)
    (withInitialComparisonTarget_preservesCardinalFilteredColimits h I hI J)
  intro j
  change IsWeakHomotopyEquivalence
    (bousfieldKanConeComparison (kanObjectForget.mapCone (withInitialKanCone (F.obj j))))
  exact bousfieldKanComparison_of_kanCone_isLimit _ (hc j)

end SerrePositivity.InfinityCategories.F2.Presentable
