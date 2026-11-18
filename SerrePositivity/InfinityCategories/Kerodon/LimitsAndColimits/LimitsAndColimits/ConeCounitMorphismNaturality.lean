module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.ConeCounitHomUniversal
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHomEvaluation

/-!
概要：任意の錐の全図式間の変換に対する、元の錐の余単位の自然性。
方針：錐の形の定値始点から底へのホモトピーの前合成作用を使い、同じ端点で正規化する。
使われ方：HTT 6.2.2.6、Kerodon §7.1（Tag 02H1）の降下と極限の比較。
規約：錐の極限性や変換の可逆性は仮定しない。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions
open SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
open SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories
open SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits

/-- 元の二つの錐の全変換は、頂点での変換と底での変換を余単位で可換にする。 -/
lemma coneCounitHom_morphism_naturality {K X : SSet.{u}} [Quasicategory X]
    {p q : K ⟶ X} (c : JoinCone p) (d : JoinCone q) (α : FunctorHom c.val d.val) :
    constantFunctorHomMap K
      (functorHomEvaluate α (SSet.yonedaEquiv (joinInl (Δ[0] : SSet.{u}) K))) ≫
        coneCounitHom d = coneCounitHom c ≫
          kanFunctorHomCongr c.property d.property
            ((hoFunctor.map ((pre (joinInr (Δ[0] : SSet.{u}) K)).app X)).toFunctor.map α) := by
  let x := SSet.yonedaEquiv (joinInl (Δ[0] : SSet.{u}) K)
  have hn := (precompositionNatTrans (coneDomainHomotopy K) X).naturality α
  erw [precompositionNatTrans_app, precompositionNatTrans_app] at hn
  have h := congrArg (kanFunctorHomCongr (SSet.const_comp x c.val) d.property) hn
  rw [← functorHomEvaluate_constantFunctorHomMap K α x]
  simpa only [x, constantFunctorCompIso, coneCounitHom, kanFunctorHomCongr,
    Iso.homCongr_apply, eqToIso.inv, eqToIso.hom, Category.assoc, eqToHom_trans_assoc,
    eqToHom_trans, eqToHom_refl, Category.id_comp] using h

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
