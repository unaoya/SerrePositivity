module
public import SerrePositivity.KST.NonConnective.DGKappaSuspensionInverseDescent
public import SerrePositivity.KST.NonConnective.DGKappaSuspensionProjectionNaturality

/-!
概要：perfect を反映する cone 同値の、元の実懸垂入力射が全 ∞ 圏同値となる。
方針：同じ商に下降した逆射との二合成を、元の商射への前合成から反映する。
規約：同じ厳密 dg 入力射を順射として保持する。別の模型選択同値へ置換しない。
使われ方：K-7 e の実 Morita 懸垂射と、元の固定 K への比較の接続。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.NonConnective
variable (R : Type u) [CommRing R] (C D : Type v)
  [DGCategory R C] [Small.{u} C] [DGCategory R D] [Small.{u} D]
  {κ : Cardinal.{u}} (I : DGKappaConeInput R C κ) (J : DGKappaConeInput R D κ)
  (M : DGKappaSuspensionMapData R C D I J)
  (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map M.cone))
  (hr : ∀ x : DGKappaCone R C I,
    M.cone.obj x ∈ dgKappaConePerfectObjects R D J → x ∈ dgKappaConePerfectObjects R C I)
local instance moritaQuotientSourceStable : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable (dgKappaSuspensionInfinity R C I) :=
  dgKappaSuspensionInfinity_isStable R C I
local instance moritaQuotientTargetStable : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable (dgKappaSuspensionInfinity R D J) :=
  dgKappaSuspensionInfinity_isStable R D J

local instance moritaQuotientSourceInputStable :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (dgKappaSuspensionKInput R C I)) :=
  dgKappaSuspensionInfinity_isStable R C I
local instance moritaQuotientTargetInputStable :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (dgKappaSuspensionKInput R D J)) :=
  dgKappaSuspensionInfinity_isStable R D J

/-- 元の厳密懸垂入力射の後の同じ下降逆射は、源の実商の恒等関手と同型。 -/
def dgKappaSuspensionMorita_leftIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgKappaSuspensionInputMap R C D I J M).down ≫
      dgKappaSuspensionInverseMap R C D I J M hf hr) (𝟙 _) := by
  let F := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgKappaSuspensionInputMap R C D I J M).down
  let G := dgKappaSuspensionInverseMap R C D I J M hf hr
  let E := hf.choose
  let : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor F := dgKappaSuspensionInputMap_isExact R C D I J M
  let : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor G := dgKappaSuspensionInverseMap_isExact R C D I J M hf hr
  apply dgKappaSuspensionFunctorIso_of_precomp R C I _ (F ≫ G) (𝟙 _)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.isExactFunctor_comp F G) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.isExactFunctor_id _)
  have e₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (dgKappaSuspensionProjection R C I ≫ (F ≫ G))
      (E.hom ≫ (dgKappaSuspensionProjection R D J ≫ G)) := by
    simpa only [Category.assoc, F, E] using!
      (dgKappaSuspensionProjectionNaturality R C D I J M).postcomp G
  have e₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (E.hom ≫ (dgKappaSuspensionProjection R D J ≫ G))
      (E.hom ≫ (E.inv ≫ dgKappaSuspensionProjection R C I)) :=
    (dgKappaSuspensionInverseMap_facIso R C D I J M hf hr).precomp E.hom
  have e₂ : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (E.hom ≫ (E.inv ≫ dgKappaSuspensionProjection R C I))
      (dgKappaSuspensionProjection R C I) := by
    simpa only [Category.assoc, Category.id_comp] using!
      E.homInvIso.postcomp (dgKappaSuspensionProjection R C I)
  simpa only [Category.comp_id] using! e₀ ≪≫ e₁ ≪≫ e₂

/-- 同じ下降逆射の後の元の厳密懸垂入力射も、標的の実商の恒等関手と同型。 -/
def dgKappaSuspensionMorita_rightIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (dgKappaSuspensionInverseMap R C D I J M hf hr ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgKappaSuspensionInputMap R C D I J M).down) (𝟙 _) := by
  let F := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgKappaSuspensionInputMap R C D I J M).down
  let G := dgKappaSuspensionInverseMap R C D I J M hf hr
  let E := hf.choose
  let : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor F := dgKappaSuspensionInputMap_isExact R C D I J M
  let : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor G := dgKappaSuspensionInverseMap_isExact R C D I J M hf hr
  apply dgKappaSuspensionFunctorIso_of_precomp R D J _ (G ≫ F) (𝟙 _)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.isExactFunctor_comp G F) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.isExactFunctor_id _)
  have e₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (dgKappaSuspensionProjection R D J ≫ (G ≫ F))
      (E.inv ≫ (dgKappaSuspensionProjection R C I ≫ F)) := by
    simpa only [Category.assoc, G, E] using!
      (dgKappaSuspensionInverseMap_facIso R C D I J M hf hr).postcomp F
  have e₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (E.inv ≫ (dgKappaSuspensionProjection R C I ≫ F))
      (E.inv ≫ (E.hom ≫ dgKappaSuspensionProjection R D J)) :=
    (dgKappaSuspensionProjectionNaturality R C D I J M).precomp E.inv
  have e₂ : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (E.inv ≫ (E.hom ≫ dgKappaSuspensionProjection R D J))
      (dgKappaSuspensionProjection R D J) := by
    simpa only [Category.assoc, Category.id_comp] using!
      E.invHomIso.postcomp (dgKappaSuspensionProjection R D J)
  simpa only [Category.comp_id] using! e₀ ≪≫ e₁ ≪≫ e₂

/-- 同じ元の厳密な懸垂入力射を順射として保つ、実懸垂商の同値。 -/
def dgKappaSuspensionMoritaEquivalence :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence (dgKappaSuspensionInfinity R C I) (dgKappaSuspensionInfinity R D J) :=
  ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgKappaSuspensionInputMap R C D I J M).down,
    dgKappaSuspensionInverseMap R C D I J M hf hr,
    dgKappaSuspensionMorita_leftIso R C D I J M hf hr,
    dgKappaSuspensionMorita_rightIso R C D I J M hf hr⟩

include hf hr in
/-- 元の同じ実懸垂入力射の nerve が全 ∞ 圏同値となる。 -/
theorem dgKappaSuspensionInputMap_isQCatEquivalence :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgKappaSuspensionInputMap R C D I J M).down) :=
  (dgKappaSuspensionMoritaEquivalence R C D I J M hf hr).isQCatEquivalence

end SerrePositivity.KST.NonConnective
