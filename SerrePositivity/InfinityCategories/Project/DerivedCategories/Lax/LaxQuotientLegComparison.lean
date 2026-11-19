module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias

public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.SuspensionExactFunctor
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.LaxCounitQuotientComparison
public import SerrePositivity.KST.LocalizingInvariants.LaxInclusions
public import SerrePositivity.KST.LocalizingInvariants.StableValueFunctor

/-!
概要：一般商の元の二脚は、Verdier 包含に沿って全関手同型で可換する。
方針：余単位の商での cofiber を両側から比較し、Q の suspension 同値で打ち消す。
規約：整数 π だけの比較ではない。使われ方：不変量の値の実 cospan 錐。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open SerrePositivity.InfinityCategories SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.LocalizingInvariants
end SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax
open _root_.SerrePositivity.KST.LocalizingInvariants
variable {C D E A Q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (p : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap C E) (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap D E)
  (i : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A (laxCategory p q)) (r : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap (laxCategory p q) Q)
  (h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence i r)

def laxQuotientLegsIso : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
    ((i.hom ≫ (laxFst p q).hom) ≫ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.laxQuotientCLeg p q r).hom)
    ((i.hom ≫ (laxSnd p q).hom) ≫ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.laxQuotientDLeg p q r).hom) := by
  apply ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.SuspensionExactDiagrams.equivalence Q.obj).isQCatEquivalence.postcompose A.obj
    ).isFullyFaithful.preimageVertexIso
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
    (((i.hom ≫ (laxFst p q).hom) ≫ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.laxQuotientCLeg p q r).hom) ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.map Q.obj)
    (((i.hom ≫ (laxSnd p q).hom) ≫ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.laxQuotientDLeg p q r).hom) ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.map Q.obj)
  have ec : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
      (((i.hom ≫ (laxFst p q).hom) ≫ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.laxQuotientCLeg p q r).hom) ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.map Q.obj)
      ((i.hom ≫ (laxFst p q).hom) ≫ (LaxInclusion.fromC p q ≫ r.hom)) := by
    simpa only [Category.assoc] using _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.precomp
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.laxQuotientCLeg_suspensionIso p q r) (i.hom ≫ (laxFst p q).hom)
  exact ec ≪≫ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.quotientCofiber_CIso p q i r).symm ≪≫
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.quotientCofiber_DSuspIso p q i r h

variable (Φ : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u} ⟶ Sp.{u})

include h in
lemma valueMap_laxQuotientLegs_comm :
    SpectrumHo.hom (valueMap Φ i ≫ valueMap Φ (laxFst p q)) ≫
        SpectrumHo.hom (valueMap Φ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.laxQuotientCLeg p q r)) =
      SpectrumHo.hom (valueMap Φ i ≫ valueMap Φ (laxSnd p q)) ≫
        SpectrumHo.hom (valueMap Φ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.laxQuotientDLeg p q r)) := by
  rw [SpectrumHo.hom_comp, SpectrumHo.hom_comp]
  change ((stableValueFunctor Φ).map i ≫ (stableValueFunctor Φ).map (laxFst p q)) ≫
      (stableValueFunctor Φ).map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.laxQuotientCLeg p q r) =
    ((stableValueFunctor Φ).map i ≫ (stableValueFunctor Φ).map (laxSnd p q)) ≫
      (stableValueFunctor Φ).map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.laxQuotientDLeg p q r)
  let f : A ⟶ Q := (i ≫ laxFst p q) ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.laxQuotientCLeg p q r
  let g : A ⟶ Q := (i ≫ laxSnd p q) ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.laxQuotientDLeg p q r
  have e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f.hom g.hom := by
    change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso ((i.hom ≫ (laxFst p q).hom) ≫ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.laxQuotientCLeg p q r).hom)
      ((i.hom ≫ (laxSnd p q).hom) ≫ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.laxQuotientDLeg p q r).hom)
    exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.laxQuotientLegsIso p q i r h
  have he := valueMap_hom_eq_of_functorIso Φ e
  change (stableValueFunctor Φ).map f = (stableValueFunctor Φ).map g at he
  simpa only [f, g, CategoryTheory.Functor.map_comp] using he

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section
