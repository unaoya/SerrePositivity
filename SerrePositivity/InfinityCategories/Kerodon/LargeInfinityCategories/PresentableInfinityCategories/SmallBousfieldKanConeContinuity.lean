module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.SmallBousfieldKanContinuity
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FilteredPointwiseWeakEquivalences
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.ConeComparisonReflection

/-!
概要：小さい poset 上の錐の Bousfield–Kan 比較の弱同値性は μ-filtered 余極限で保たれる。
方針：錐族を厳密極限への自然変換として保持し、元の比較射と余極限比較の一致を証明する。
規約：strict な錐族の主張。native な全 coherent 錐の極限性との同一視は別途必要。
使われ方：μ-small 部分余極限の compact 性に必要な極限・余極限交換。

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

/-- 指定自然変換が与える各段階の元の錐。 -/
def cardinalFilteredConeStage (F : J ⥤ I ⥤ SSet.{u})
    {X : J ⥤ SSet.{u}} (σ : X ⟶ F ⋙ lim) (j : J) : Cone (F.obj j) :=
  (limit.cone (F.obj j)).extend (σ.app j)

/-- 元の strict 錐族の標準比較射を、一つの自然変換として保持する。 -/
def bousfieldKanConeFamilyComparison (F : J ⥤ I ⥤ SSet.{u})
    {X : J ⥤ SSet.{u}} (σ : X ⟶ F ⋙ lim) :
    X ⟶ F ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanHolimFunctor I :=
  σ ≫ {
    app := fun j ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanLimitComparison (F.obj j)
    naturality := fun _ _ f ↦
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanLimitComparison_naturality (F.map f)).symm }

/-- 錐族の比較の各成分は、指定された元の段階錐の比較射そのもの。 -/
lemma bousfieldKanConeFamilyComparison_app (F : J ⥤ I ⥤ SSet.{u})
    {X : J ⥤ SSet.{u}} (σ : X ⟶ F ⋙ lim) (j : J) :
    (bousfieldKanConeFamilyComparison F σ).app j =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanConeComparison (cardinalFilteredConeStage F σ j) := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanConeComparison_limitLift]
  have hl : limit.lift (F.obj j) (cardinalFilteredConeStage F σ j) = σ.app j := by
    apply limit.hom_ext
    intro i
    simp [cardinalFilteredConeStage]
  rw [hl]
  rfl

/-- 同じ錐族の余極限。頂点は元の頂点族の strict な余極限そのもの。 -/
def cardinalFilteredConeColimit (F : J ⥤ I ⥤ SSet.{u})
    {X : J ⥤ SSet.{u}} (σ : X ⟶ F ⋙ lim) : Cone (colimit F) :=
  (limit.cone (colimit F)).extend (colim.map σ ≫ colimit.post F lim)

/-- 余極限への各元の脚は段階錐の全成分を厳密に回収する。 -/
lemma cardinalFilteredConeColimit_ι_π (F : J ⥤ I ⥤ SSet.{u})
    {X : J ⥤ SSet.{u}} (σ : X ⟶ F ⋙ lim) (j : J) (i : I) :
    colimit.ι X j ≫ (cardinalFilteredConeColimit F σ).π.app i =
      (cardinalFilteredConeStage F σ j).π.app i ≫ (colimit.ι F j).app i := by
  simp [cardinalFilteredConeColimit, cardinalFilteredConeStage, Category.assoc]

/-- 余極限錐の元の比較は、各段階の比較の余極限と標準保存比較の合成に等しい。 -/
lemma cardinalFilteredConeColimit_comparison (F : J ⥤ I ⥤ SSet.{u})
    {X : J ⥤ SSet.{u}} (σ : X ⟶ F ⋙ lim) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanConeComparison (cardinalFilteredConeColimit F σ) =
      colim.map (bousfieldKanConeFamilyComparison F σ) ≫
        colimit.post F (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanHolimFunctor I) := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanConeComparison_limitLift]
  have hl : limit.lift (colimit F) (cardinalFilteredConeColimit F σ) =
      colim.map σ ≫ colimit.post F lim := by
    apply limit.hom_ext
    intro i
    simp [cardinalFilteredConeColimit]
  rw [hl]
  apply colimit.hom_ext
  intro j
  simp only [Category.assoc, colimit.ι_map_assoc, colimit.ι_post_assoc,
    bousfieldKanConeFamilyComparison, NatTrans.comp_app]
  rw [colimit.ι_post]
  exact congrArg (σ.app j ≫ ·)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanLimitComparison_naturality (colimit.ι F j)).symm

variable {κ μ : Cardinal.{u}} [Fact κ.IsRegular] [Fact μ.IsRegular]

/-- 小さい poset 上で各段階の元の比較が弱同値なら、同じ余極限錐の比較も弱同値。 -/
lemma cardinalFilteredConeColimit_comparison_isWeakHomotopyEquivalence
    (h : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IsCardinalChangeBound κ μ) (I : Type u) [PartialOrder I]
    (hI : HasCardinalLT I μ) (J : Type u) [SmallCategory J]
    [IsCardinalFiltered J μ] (F : J ⥤ I ⥤ SSet.{u})
    {X : J ⥤ SSet.{u}} (σ : X ⟶ F ⋙ lim)
    (hσ : ∀ j, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanConeComparison (cardinalFilteredConeStage F σ j))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanConeComparison (cardinalFilteredConeColimit F σ)) := by
  have := isFiltered_of_isCardinalFiltered J μ
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.bousfieldKanHolimFunctor_poset_preservesCardinalFilteredColimits h I hI J
  rw [cardinalFilteredConeColimit_comparison]
  have hStages : ∀ j, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence
      ((bousfieldKanConeFamilyComparison F σ).app j) := by
    intro j
    rw [bousfieldKanConeFamilyComparison_app]
    exact hσ j
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.filteredColimitMap_isWeakHomotopyEquivalence_of_pointwise _ hStages).comp
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_of_iso
    (asIso (colimit.post F (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanHolimFunctor I)))).isWeakHomotopyEquivalence

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
