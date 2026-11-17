module

public import SerrePositivity.EInfinity.BarrattEccles.Modules.RawModuleComparison
public import SerrePositivity.EInfinity.Modules.LocalizationSourceNaturality
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UniversalConsequences

/-!
# 同じ降下比較と制限の全自然性

概要：M10/C02 の比較を元の全厳密 BE 制限と全関手間で照合する。
方針：通常源で同じ三角を貼り、実局所化の前合成の充満忠実性で降ろす。
規約：HA §4.2.3、半自由性を制限が保つという仮定は置かない。
使われ方：同じ全族の fiber 比較の係数自然性。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory SSet MonoidalClosed
open SerrePositivity.EInfinity.Modules
open _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization
open SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories
open FullFaithfulAndEssentiallySurjectiveFunctors
open scoped Simplicial
variable (A : Type u) [CommRing A]

/-- 概要：同じ通常局所化源上の全関手同型を元の局所化上へ降ろす。
方針：前合成の充満忠実性から同じ同型の逆像を取る。
規約：HA 1.3.4.1 の成分。使われ方：同じ制限比較の全単体の降下。 -/
def strictRawModuleLocalization_descendIso (X : (operad A).Algebra)
    {Y : SSet.{u+1}} [Quasicategory Y]
    {F G : _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationNerve (strictRawModuleRelativeCategory A X) ⟶ Y}
    (e : FunctorIso
      (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationNerveSourceMap (strictRawModuleRelativeCategory A X) ≫ F)
      (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationNerveSourceMap (strictRawModuleRelativeCategory A X) ≫ G)) :
    FunctorIso F G := by
  let q := _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationNerveSourceMap (strictRawModuleRelativeCategory A X)
  let ff := (UniversalConsequences.IsLocalization.precomposition_isFullyFaithful
    (strictRawModuleLocalization_isLocalization A X) Y).toHoFullyFaithful
  apply ff.preimageIso
  change VertexIso
    (((pre q).app Y).app (Opposite.op ⦋0⦌) (functorVertex F))
    (((pre q).app Y).app (Opposite.op ⦋0⦌) (functorVertex G))
  rw [MorphismSpaces.functorVertex_precomposition, MorphismSpaces.functorVertex_precomposition]
  exact e

/-- 概要：同じ比較と制限の三角は通常源上で全関手同型。
方針：源の係数自然性・両方の指定三角・同じ制限の比較を順に貼る。
規約：HA §4.2.3、元の全厳密 BE 代数射。使われ方：同じ比較の局所化への降下。 -/
def strictRawModuleComparison_restrictSourceIso {X Y : (operad A).Algebra} (f : X ⟶ Y) :
    FunctorIso
      (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationNerveSourceMap (strictRawModuleRelativeCategory A Y) ≫
        _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationNerveMap (strictRawModuleRestrictRelative f) ≫ strictRawModuleComparison A X)
      (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationNerveSourceMap (strictRawModuleRelativeCategory A Y) ≫
        strictRawModuleComparison A Y ≫ strictModuleRestrict f) := by
  let N := nerveMap (strictRawModuleRestrictRelative f).functor
  have e₀ := (localizationNerveSourceNaturalityIso (strictRawModuleRestrictRelative f)).postcomp
    (strictRawModuleComparison A X)
  have e₁ := (strictRawModuleComparison_sourceIso A X).precomp N
  have e₂ := strictRawModuleSource_restrictIso A f
  have e₃ := ((strictRawModuleComparison_sourceIso A Y).postcomp (strictModuleRestrict f)).symm
  simpa only [N, Category.assoc] using e₀ ≪≫ e₁ ≪≫ e₂ ≪≫ e₃

/-- 概要：同じ比較は全ての厳密 BE 制限と全関手間で可換。
方針：同じ通常源上の三角比較を、実局所化の充満忠実性で降ろす。
規約：HA §4.2.3、別の制限を選び直さない。使われ方：C02 の全係数自然性。 -/
def strictRawModuleComparison_restrictIso {X Y : (operad A).Algebra} (f : X ⟶ Y) :
    FunctorIso
      (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationNerveMap (strictRawModuleRestrictRelative f) ≫ strictRawModuleComparison A X)
      (strictRawModuleComparison A Y ≫ strictModuleRestrict f) :=
  strictRawModuleLocalization_descendIso A Y (strictRawModuleComparison_restrictSourceIso A f)

end SerrePositivity.EInfinity.BarrattEccles
