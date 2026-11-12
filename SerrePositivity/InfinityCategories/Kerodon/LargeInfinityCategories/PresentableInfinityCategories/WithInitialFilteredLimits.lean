module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.FilteredComparisonContinuity
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.WithInitialKanCone
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.KanFamilyColimit

/-!
概要：WithInitial の共同 Kan 図式の各段階の native 極限性は、同じ関手圏の μ-filtered 余極限へ移る。
方針：元の錐の比較射を二つの連続関手間の自然変換にし、その余極限成分の弱同値性を検証する。
規約：頂点・図式・全脚は元の strict 余極限図式そのもの。
使われ方：coherent な錐族の模型の極限性を、元の指定された点ごとの余極限余錐へ戻す。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

variable (I : Type u) [SmallCategory I]

/-- 元の WithInitial の単体集合値図式から、同じ頂点・脚の錐を読む。 -/
def withInitialSSetCone (H : WithInitial I ⥤ SSet.{u}) : Cone (WithInitial.incl ⋙ H) where
  pt := H.obj WithInitial.star
  π := (WithInitial.mkCommaObject H).hom

/-- 元の錐の比較射は、始対象評価と同じ Bousfield–Kan 模型との間の一つの自然変換。 -/
def withInitialConeComparison :
    (evaluation (WithInitial I) SSet.{u}).obj WithInitial.star ⟶
      (Functor.whiskeringLeft I (WithInitial I) SSet.{u}).obj WithInitial.incl ⋙
        _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanHolimFunctor I where
  app H := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanConeComparison (withInitialSSetCone I H)
  naturality H H' η := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedConeComparison_naturality (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight I)
    (withInitialSSetCone I H) (withInitialSSetCone I H') (η.app WithInitial.star)
    (Functor.whiskerLeft WithInitial.incl η)
    (fun i ↦ (η.naturality (WithInitial.starInitial.to (WithInitial.of i))).symm)

variable {κ μ : Cardinal.{u}} [Fact κ.IsRegular] [Fact μ.IsRegular]

/-- 元の比較の標的関手は、小さい poset 上で μ-filtered 余極限を保つ。 -/
lemma withInitialComparisonTarget_preservesCardinalFilteredColimits
    (h : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IsCardinalChangeBound κ μ) (I : Type u) [PartialOrder I] (hI : HasCardinalLT I μ)
    (J : Type u) [SmallCategory J] [IsCardinalFiltered J μ] :
    PreservesColimitsOfShape J
      ((Functor.whiskeringLeft I (WithInitial I) SSet.{u}).obj WithInitial.incl ⋙
        _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanHolimFunctor I) := by
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.bousfieldKanHolimFunctor_poset_preservesCardinalFilteredColimits h I hI J
  infer_instance

/-- 元の共同 WithInitial 図式の strict 余極限の錐自身が native な極限錐。 -/
lemma withInitialFilteredColimit_isLimit
    (h : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IsCardinalChangeBound κ μ) (I : Type u) [PartialOrder I] (hI : HasCardinalLT I μ)
    (J : Type u) [SmallCategory J] [IsCardinalFiltered J μ]
    (F : J ⥤ WithInitial I ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u})
    (hc : ∀ j, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.withInitialKanCone (F.obj j)))) :
    letI := isFiltered_of_isCardinalFiltered J μ
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.withInitialKanCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.cardinalFilteredKanDiagram F))) := by
  have := isFiltered_of_isCardinalFiltered J μ
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.kanCone_isLimit_of_bousfieldKanComparison
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence
    ((withInitialConeComparison I).app (colimit (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.kanConeFamilyUnderlying F)))
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.comparison_colimit_isWeakHomotopyEquivalence
    (withInitialConeComparison I) (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.kanConeFamilyUnderlying F) (by infer_instance)
    (withInitialComparisonTarget_preservesCardinalFilteredColimits h I hI J)
  intro j
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanConeComparison (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget.mapCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.withInitialKanCone (F.obj j))))
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanComparison_of_kanCone_isLimit _ (hc j)

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
