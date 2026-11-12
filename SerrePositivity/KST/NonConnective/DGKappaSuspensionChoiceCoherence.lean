module
public import SerrePositivity.KST.NonConnective.DGKappaSuspensionChoiceEquivalence

/-!
概要：実平坦懸垂の選択比較の恒等・三選択合成を、元の商射に沿って照合する。
方針：実 cone の指定比較を商の全完全関手圏の充満忠実性で反映する。
規約：固定 κ と元の商射を保持する。異なる dg 入力の作用や反復構造辺は別工程。
使われ方：K-7 d4 の選択比較・下降の整合と全高次パラメータへの再制限。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.NonConnective
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {κ : Cardinal.{u}} (I J K : DGKappaConeInput R D κ)
  (P : DGKappaPerfectInput R D I) (Q : DGKappaPerfectInput R D J)
  (T : DGKappaPerfectInput R D K)
local instance suspensionChoiceCoherenceStable (L : DGKappaConeInput R D κ) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable (dgKappaSuspensionInfinity R D L) := dgKappaSuspensionInfinity_isStable R D L

/-- 同一選択の実下降比較は、元の実商の恒等関手と同型。 -/
def dgKappaSuspensionChoiceMap_selfIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (dgKappaSuspensionChoiceMap R D I I P P)
      (𝟙 (dgKappaSuspensionInfinity R D I)) := by
  apply dgKappaSuspensionFunctorIso_of_precomp R D I _ _ _
    (dgKappaSuspensionChoiceMap_isExact R D I I P P) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.isExactFunctor_id _)
  have e := (dgKappaSuspensionChoiceMap_facIso R D I I P P) ≪≫
    (dgKappaConeChoiceEquivalence_selfIso R D I).postcomp
      (dgKappaSuspensionProjection R D I)
  simpa only [Category.id_comp, Category.comp_id] using! e

/-- 三つの選択の実下降射は、同じ cone 比較の合成二胞体と整合する。 -/
def dgKappaSuspensionChoiceMap_compIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (dgKappaSuspensionChoiceMap R D I J P Q ≫
      dgKappaSuspensionChoiceMap R D J K Q T) (dgKappaSuspensionChoiceMap R D I K P T) := by
  let F := dgKappaSuspensionChoiceMap R D I J P Q
  let G := dgKappaSuspensionChoiceMap R D J K Q T
  let H := dgKappaSuspensionChoiceMap R D I K P T
  let : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor F := dgKappaSuspensionChoiceMap_isExact R D I J P Q
  let : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor G := dgKappaSuspensionChoiceMap_isExact R D J K Q T
  apply dgKappaSuspensionFunctorIso_of_precomp R D I _ (F ≫ G) H
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.isExactFunctor_comp F G) (dgKappaSuspensionChoiceMap_isExact R D I K P T)
  have e₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (dgKappaSuspensionProjection R D I ≫ (F ≫ G))
      ((dgKappaConeChoiceEquivalence R D I J).hom ≫
        (dgKappaSuspensionProjection R D J ≫ G)) := by
    simpa only [Category.assoc, F] using!
      (dgKappaSuspensionChoiceMap_facIso R D I J P Q).postcomp G
  have e₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
      ((dgKappaConeChoiceEquivalence R D I J).hom ≫
        (dgKappaSuspensionProjection R D J ≫ G))
      ((dgKappaConeChoiceEquivalence R D I J).hom ≫
        ((dgKappaConeChoiceEquivalence R D J K).hom ≫
          dgKappaSuspensionProjection R D K)) := by
    simpa only [G] using!
      (dgKappaSuspensionChoiceMap_facIso R D J K Q T).precomp
        (dgKappaConeChoiceEquivalence R D I J).hom
  have e₂ : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
      ((dgKappaConeChoiceEquivalence R D I J).hom ≫
        ((dgKappaConeChoiceEquivalence R D J K).hom ≫
          dgKappaSuspensionProjection R D K))
      ((dgKappaConeChoiceEquivalence R D I K).hom ≫
        dgKappaSuspensionProjection R D K) := by
    simpa only [Category.assoc] using!
      (dgKappaConeChoiceEquivalence_compIso R D I J K).postcomp
        (dgKappaSuspensionProjection R D K)
  exact e₀ ≪≫ e₁ ≪≫ e₂ ≪≫ (dgKappaSuspensionChoiceMap_facIso R D I K P T).symm

/-- 同じ実下降比較は、任意の全高次パラメータ族に前合成できる。 -/
def dgKappaSuspensionChoiceParameterIso {S : SSet.{max (u + 1) v}}
    (a : S ⟶ dgKappaSuspensionInfinity R D I) :=
  (dgKappaSuspensionChoiceMap_compIso R D I J K P Q T).precomp a

/-- 任意族の再制限では、同じ指定比較の前合成を厳密に回収する。 -/
theorem dgKappaSuspensionChoiceParameterIso_precomp {S U : SSet.{max (u + 1) v}}
    (a : S ⟶ dgKappaSuspensionInfinity R D I) (r : U ⟶ S) :
    (dgKappaSuspensionChoiceParameterIso R D I J K P Q T a).precomp r =
      dgKappaSuspensionChoiceParameterIso R D I J K P Q T (r ≫ a) :=
  _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_precomp_precomp _ _ _

end SerrePositivity.KST.NonConnective
