module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.KanConeComparisonCriterion
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.SmallBousfieldKanConeContinuity
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.KanDiagramOfSSet

/-!
概要：小さい poset 上の Kan 値 strict 極限錐族の μ-filtered 余極限は native な極限錐。
方針：同じ頂点と脚の余極限を束縛し、元の比較の保存と全錐の判定を合成する。
規約：strict な錐族を扱う。任意の coherent な族の同時 strictification は別途必要。
使われ方：accessible 圏の濃度変更で使う Space の小さい極限と filtered 余極限の交換。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

variable {I J : Type u} [SmallCategory I] [SmallCategory J]

/-- 元の Kan 図式族の台を一つの strict な図式族として保持する。 -/
def kanConeFamilyUnderlying (F : J ⥤ I ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) : J ⥤ I ⥤ SSet.{u} :=
  F ⋙ (Functor.whiskeringRight I _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u} SSet.{u}).obj _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget

/-- 元の頂点族と指定錐族の各段階を、そのまま Kan 対象の錐に束縛する。 -/
def cardinalFilteredKanConeStage (F : J ⥤ I ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) (X : J ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u})
    (σ : X ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget ⟶ kanConeFamilyUnderlying F ⋙ lim) (j : J) : Cone (F.obj j) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.kanObjectConeOfUnderlying (F.obj j)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.cardinalFilteredConeStage (kanConeFamilyUnderlying F) σ j)
    (inferInstanceAs (KanComplex (X.obj j).obj))

/-- 忘却すると、指定された元の段階錐を厳密に回収する。 -/
lemma cardinalFilteredKanConeStage_forget (F : J ⥤ I ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u})
    (X : J ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u})
    (σ : X ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget ⟶ kanConeFamilyUnderlying F ⋙ lim) (j : J) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget.mapCone (cardinalFilteredKanConeStage F X σ j) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.cardinalFilteredConeStage (kanConeFamilyUnderlying F) σ j := rfl

variable [IsFiltered J]

/-- 評価と余極限の標準同型から、同じ余極限図式の各値は Kan。 -/
lemma kanConeFamilyColimit_kanComplex (F : J ⥤ I ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) (i : I) :
    KanComplex ((colimit (kanConeFamilyUnderlying F)).obj i) := by
  have (j : J) : KanComplex
      (((kanConeFamilyUnderlying F) ⋙ (evaluation I SSet.{u}).obj i).obj j) :=
    inferInstanceAs (KanComplex ((F.obj j).obj i).obj)
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.kanComplex_of_iso
    (colimitObjIsoColimitCompEvaluation (kanConeFamilyUnderlying F) i).symm

/-- 元の strict な余極限図式を Kan 対象へ束縛する。 -/
def cardinalFilteredKanDiagram (F : J ⥤ I ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) : I ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u} := by
  have := kanConeFamilyColimit_kanComplex F
  exact _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.kanDiagramOfSSet (colimit (kanConeFamilyUnderlying F))

/-- 頂点族と脚の元の余極限を持つ Kan 値の錐。 -/
def cardinalFilteredKanConeColimit (F : J ⥤ I ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) (X : J ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u})
    (σ : X ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget ⟶ kanConeFamilyUnderlying F ⋙ lim) :
    Cone (cardinalFilteredKanDiagram F) := by
  have (j : J) : KanComplex ((X ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget).obj j) :=
    inferInstanceAs (KanComplex (X.obj j).obj)
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.kanObjectConeOfUnderlying (cardinalFilteredKanDiagram F)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.cardinalFilteredConeColimit (kanConeFamilyUnderlying F) σ)
    (inferInstanceAs (KanComplex (colimit (X ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget))))

/-- 忘却すると、頂点も全ての脚も元の strict な余極限錐そのもの。 -/
lemma cardinalFilteredKanConeColimit_forget (F : J ⥤ I ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u})
    (X : J ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u})
    (σ : X ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget ⟶ kanConeFamilyUnderlying F ⋙ lim) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget.mapCone (cardinalFilteredKanConeColimit F X σ) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.cardinalFilteredConeColimit (kanConeFamilyUnderlying F) σ := rfl

variable {κ μ : Cardinal.{u}} [Fact κ.IsRegular] [Fact μ.IsRegular]

/-- 各段階で実際の ∞ 極限錐である指定 strict 錐族の余極限も、同じ図式の ∞ 極限錐。 -/
lemma cardinalFilteredKanConeColimit_isLimit
    (h : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IsCardinalChangeBound κ μ) (I : Type u) [PartialOrder I]
    (hI : HasCardinalLT I μ) (J : Type u) [SmallCategory J] [IsCardinalFiltered J μ]
    (F : J ⥤ I ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) (X : J ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u})
    (σ : X ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget ⟶ kanConeFamilyUnderlying F ⋙ lim)
    (hc : ∀ j, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentCone (cardinalFilteredKanConeStage F X σ j))) :
    letI := isFiltered_of_isCardinalFiltered J μ
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentCone (cardinalFilteredKanConeColimit F X σ)) := by
  have := isFiltered_of_isCardinalFiltered J μ
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.kanCone_isLimit_of_bousfieldKanComparison
  rw [cardinalFilteredKanConeColimit_forget]
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.cardinalFilteredConeColimit_comparison_isWeakHomotopyEquivalence h I hI J _ σ
  intro j
  have hj := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanComparison_of_kanCone_isLimit
    (cardinalFilteredKanConeStage F X σ j) (hc j)
  rw [cardinalFilteredKanConeStage_forget] at hj
  exact hj

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
