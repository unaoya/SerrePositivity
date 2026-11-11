module
public import SerrePositivity.KST.NonConnective.DGKappaSuspensionChoiceMap

/-!
概要：固定 κ の二つの実平坦懸垂の選択比較が、元の商射を保つ同値であることを証明する。
方針：実 cone 比較の逆二胞体を、同じ商の全完全関手圏の充満忠実性で反映する。
規約：現行 I・P を保持し、strict dg 比較や K の反復構造辺の自然性は推論しない。
使われ方：K-7 d4・e の実商の模型選択不変性。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.NonConnective
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {κ : Cardinal.{u}} (I J : DGKappaConeInput R D κ)
  (P : DGKappaPerfectInput R D I) (Q : DGKappaPerfectInput R D J)
local instance choiceEquivalenceSuspensionStable (L : DGKappaConeInput R D κ) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable (dgKappaSuspensionInfinity R D L) := dgKappaSuspensionInfinity_isStable R D L

/-- 二つの元の実下降射の合成は、同じ実商の恒等関手と同型。 -/
def dgKappaSuspensionChoiceMap_inverseIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (dgKappaSuspensionChoiceMap R D I J P Q ≫
      dgKappaSuspensionChoiceMap R D J I Q P) (𝟙 (dgKappaSuspensionInfinity R D I)) := by
  let F := dgKappaSuspensionChoiceMap R D I J P Q
  let G := dgKappaSuspensionChoiceMap R D J I Q P
  let : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor F := dgKappaSuspensionChoiceMap_isExact R D I J P Q
  let : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor G := dgKappaSuspensionChoiceMap_isExact R D J I Q P
  apply dgKappaSuspensionFunctorIso_of_precomp R D I _ (F ≫ G) (𝟙 _)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.isExactFunctor_comp F G) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.isExactFunctor_id _)
  have e₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (dgKappaSuspensionProjection R D I ≫ (F ≫ G))
      ((dgKappaConeChoiceEquivalence R D I J).hom ≫
        (dgKappaSuspensionProjection R D J ≫ G)) := by
    simpa only [Category.assoc, F] using!
      (dgKappaSuspensionChoiceMap_facIso R D I J P Q).postcomp G
  have e₁ := (dgKappaSuspensionChoiceMap_facIso R D J I Q P).precomp
    (dgKappaConeChoiceEquivalence R D I J).hom
  have e₂ : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
      ((dgKappaConeChoiceEquivalence R D I J).hom ≫
        (dgKappaConeChoiceEquivalence R D J I).hom ≫ dgKappaSuspensionProjection R D I)
      (dgKappaSuspensionProjection R D I) := by
    have ec : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso ((dgKappaConeChoiceEquivalence R D I J).hom ≫
        (dgKappaConeChoiceEquivalence R D J I).hom) (𝟙 _) :=
      dgKappaConeChoiceEquivalence_compIso R D I J I ≪≫
        dgKappaConeChoiceEquivalence_selfIso R D I
    have e := ec.postcomp (dgKappaSuspensionProjection R D I)
    simpa only [Category.assoc, Category.id_comp] using! e
  simpa only [Category.comp_id] using!
    e₀ ≪≫ (by simpa only [Category.assoc, G] using! e₁) ≪≫ e₂

/-- 同じ実商の間の模型選択比較は全関手同値。 -/
def dgKappaSuspensionChoiceEquivalence :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence (dgKappaSuspensionInfinity R D I) (dgKappaSuspensionInfinity R D J) :=
  ⟨dgKappaSuspensionChoiceMap R D I J P Q, dgKappaSuspensionChoiceMap R D J I Q P,
    dgKappaSuspensionChoiceMap_inverseIso R D I J P Q,
    dgKappaSuspensionChoiceMap_inverseIso R D J I Q P⟩

/-- 同値の順射は元の指定実下降射そのもの。 -/
theorem dgKappaSuspensionChoiceEquivalence_hom :
    (dgKappaSuspensionChoiceEquivalence R D I J P Q).hom =
      dgKappaSuspensionChoiceMap R D I J P Q := rfl

end SerrePositivity.KST.NonConnective
