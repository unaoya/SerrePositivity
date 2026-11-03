module

public import SerrePositivity.InfinityCategories.F2.Presentable.KanConeComparisonCriterion
public import SerrePositivity.InfinityCategories.F2.Presentable.SmallBousfieldKanConeContinuity
public import SerrePositivity.InfinityCategories.F1.FilteredExchange.KanDiagramOfSSet

/-!
概要：小さい poset 上の Kan 値 strict 極限錐族の μ-filtered 余極限は native な極限錐。
方針：同じ頂点と脚の余極限を束縛し、元の比較の保存と全錐の判定を合成する。
規約：strict な錐族を扱う。任意の coherent な族の同時 strictification は別途必要。
使われ方：accessible 圏の濃度変更で使う Space の小さい極限と filtered 余極限の交換。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.F2.Presentable
open HomotopyLimits
variable {I J : Type u} [SmallCategory I] [SmallCategory J]

/-- 元の Kan 図式族の台を一つの strict な図式族として保持する。 -/
def kanConeFamilyUnderlying (F : J ⥤ I ⥤ KanObject.{u}) : J ⥤ I ⥤ SSet.{u} :=
  F ⋙ (Functor.whiskeringRight I KanObject.{u} SSet.{u}).obj kanObjectForget

/-- 元の頂点族と指定錐族の各段階を、そのまま Kan 対象の錐に束縛する。 -/
def cardinalFilteredKanConeStage (F : J ⥤ I ⥤ KanObject.{u}) (X : J ⥤ KanObject.{u})
    (σ : X ⋙ kanObjectForget ⟶ kanConeFamilyUnderlying F ⋙ lim) (j : J) : Cone (F.obj j) :=
  kanObjectConeOfUnderlying (F.obj j)
    (cardinalFilteredConeStage (kanConeFamilyUnderlying F) σ j)
    (inferInstanceAs (KanComplex (X.obj j).obj))

/-- 忘却すると、指定された元の段階錐を厳密に回収する。 -/
lemma cardinalFilteredKanConeStage_forget (F : J ⥤ I ⥤ KanObject.{u})
    (X : J ⥤ KanObject.{u})
    (σ : X ⋙ kanObjectForget ⟶ kanConeFamilyUnderlying F ⋙ lim) (j : J) :
    kanObjectForget.mapCone (cardinalFilteredKanConeStage F X σ j) =
      cardinalFilteredConeStage (kanConeFamilyUnderlying F) σ j := rfl

variable [IsFiltered J]

/-- 評価と余極限の標準同型から、同じ余極限図式の各値は Kan。 -/
lemma kanConeFamilyColimit_kanComplex (F : J ⥤ I ⥤ KanObject.{u}) (i : I) :
    KanComplex ((colimit (kanConeFamilyUnderlying F)).obj i) := by
  have (j : J) : KanComplex
      (((kanConeFamilyUnderlying F) ⋙ (evaluation I SSet.{u}).obj i).obj j) :=
    inferInstanceAs (KanComplex ((F.obj j).obj i).obj)
  exact kanComplex_of_iso
    (colimitObjIsoColimitCompEvaluation (kanConeFamilyUnderlying F) i).symm

/-- 元の strict な余極限図式を Kan 対象へ束縛する。 -/
def cardinalFilteredKanDiagram (F : J ⥤ I ⥤ KanObject.{u}) : I ⥤ KanObject.{u} := by
  have := kanConeFamilyColimit_kanComplex F
  exact kanDiagramOfSSet (colimit (kanConeFamilyUnderlying F))

/-- 頂点族と脚の元の余極限を持つ Kan 値の錐。 -/
def cardinalFilteredKanConeColimit (F : J ⥤ I ⥤ KanObject.{u}) (X : J ⥤ KanObject.{u})
    (σ : X ⋙ kanObjectForget ⟶ kanConeFamilyUnderlying F ⋙ lim) :
    Cone (cardinalFilteredKanDiagram F) := by
  have (j : J) : KanComplex ((X ⋙ kanObjectForget).obj j) :=
    inferInstanceAs (KanComplex (X.obj j).obj)
  exact kanObjectConeOfUnderlying (cardinalFilteredKanDiagram F)
    (cardinalFilteredConeColimit (kanConeFamilyUnderlying F) σ)
    (inferInstanceAs (KanComplex (colimit (X ⋙ kanObjectForget))))

/-- 忘却すると、頂点も全ての脚も元の strict な余極限錐そのもの。 -/
lemma cardinalFilteredKanConeColimit_forget (F : J ⥤ I ⥤ KanObject.{u})
    (X : J ⥤ KanObject.{u})
    (σ : X ⋙ kanObjectForget ⟶ kanConeFamilyUnderlying F ⋙ lim) :
    kanObjectForget.mapCone (cardinalFilteredKanConeColimit F X σ) =
      cardinalFilteredConeColimit (kanConeFamilyUnderlying F) σ := rfl

variable {κ μ : Cardinal.{u}} [Fact κ.IsRegular] [Fact μ.IsRegular]

/-- 各段階で実際の ∞ 極限錐である指定 strict 錐族の余極限も、同じ図式の ∞ 極限錐。 -/
lemma cardinalFilteredKanConeColimit_isLimit
    (h : IsCardinalChangeBound κ μ) (I : Type u) [PartialOrder I]
    (hI : HasCardinalLT I μ) (J : Type u) [SmallCategory J] [IsCardinalFiltered J μ]
    (F : J ⥤ I ⥤ KanObject.{u}) (X : J ⥤ KanObject.{u})
    (σ : X ⋙ kanObjectForget ⟶ kanConeFamilyUnderlying F ⋙ lim)
    (hc : ∀ j, IsLimitCone (strictCoherentCone (cardinalFilteredKanConeStage F X σ j))) :
    letI := isFiltered_of_isCardinalFiltered J μ
    IsLimitCone (strictCoherentCone (cardinalFilteredKanConeColimit F X σ)) := by
  have := isFiltered_of_isCardinalFiltered J μ
  apply kanCone_isLimit_of_bousfieldKanComparison
  rw [cardinalFilteredKanConeColimit_forget]
  apply cardinalFilteredConeColimit_comparison_isWeakHomotopyEquivalence h I hI J _ σ
  intro j
  have hj := bousfieldKanComparison_of_kanCone_isLimit
    (cardinalFilteredKanConeStage F X σ j) (hc j)
  rw [cardinalFilteredKanConeStage_forget] at hj
  exact hj

end SerrePositivity.InfinityCategories.F2.Presentable
