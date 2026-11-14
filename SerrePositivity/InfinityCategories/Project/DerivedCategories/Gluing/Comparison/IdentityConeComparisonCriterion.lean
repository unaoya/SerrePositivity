module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.Comparison.LocalizationProjectionComparison
public import SerrePositivity.KST.LocalizingInvariants.IdentityLaxVerdier
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.EquivalenceStability
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.EquivalenceCalculus
/-!
概要：同じ恒等 lax 比較に沿って、対角零化と実右軸の全比較から cone 関手を同定する。
方針：指定同値の実逆で関手を運び、恒等 lax 局所化を右軸で試験し、往復則で戻す。
規約：全関手同型と元の選択差を保持。使われ方：恒等 cone 比較の一般判定。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory SSet
open _root_.SerrePositivity.KST.LocalizingInvariants
open scoped _root_.Simplicial
variable (C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}) {G P : SSet.{u}}
  [Quasicategory G] [Quasicategory P] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable G] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable P]
local notation "L" => _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.obj (laxCategory (𝟙 C) (𝟙 C))
local notation "δ" => _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap.hom (exactLaxDifference (𝟙 C) (𝟙 C))
local notation "d" => _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap.hom (IdentityLax.exactDiagonal C)

def identityConeComparisonCriterion (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence G L)
    (y : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence C.obj P) (f : G ⟶ P) [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor f]
    (i j : C.obj ⟶ G)
    (hi : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (i ≫ e.hom) d)
    (hj : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso ((j ≫ e.hom) ≫ δ) (𝟙 C.obj))
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso y.hom (j ≫ f))
    (hz : ∀ x, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex ((i ≫ f).app (Opposite.op ⦋0⦌) x)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso ((e.hom ≫ δ) ≫ y.hom) f := by
  let r := e.inv ≫ f ≫ y.inv
  let k := j ≫ e.hom
  letI : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor e.inv := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.isExactFunctor_of_isQCatEquivalence e.symm.isQCatEquivalence
  letI : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor y.inv := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.isExactFunctor_of_isQCatEquivalence y.symm.isQCatEquivalence
  letI : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor (f ≫ y.inv) := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.isExactFunctor_comp _ _
  letI : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor r := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.isExactFunctor_comp _ _
  let re : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap (laxCategory (𝟙 C) (𝟙 C)) C := ⟨r, inferInstance⟩
  have hdi₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (d ≫ r) (i ≫ e.hom ≫ e.inv ≫ f ≫ y.inv) := by
    simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso, r, Category.assoc] using _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.postcomp hi.symm r
  have hdi₂ : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (i ≫ e.hom ≫ e.inv ≫ f ≫ y.inv) (i ≫ f ≫ y.inv) := by
    simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso, Category.assoc, Category.comp_id] using
      (e.homInvIso.precomp i).postcomp (f ≫ y.inv)
  have hzero : ∀ x, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex ((d ≫ r).app (Opposite.op ⦋0⦌) x) := by
    intro x
    have hx := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor.preservesZero (F := y.inv) _ (hz x)
    exact hx.of_vertexIso (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.FunctorIso.app (hdi₁.trans hdi₂) x).symm
  have hk₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (k ≫ r) (j ≫ f ≫ y.inv) := by
    simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso, k, r, Category.assoc, Category.comp_id] using
      (e.homInvIso.precomp j).postcomp (f ≫ y.inv)
  have hk₂ : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (j ≫ f ≫ y.inv) (𝟙 C.obj) := by
    have h : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (j ≫ f ≫ y.inv) (y.hom ≫ y.inv) :=
      _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.postcomp hf.symm y.inv) (Category.assoc _ _ _) rfl
    exact h.trans y.homInvIso
  have htest : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (k ≫ r) (k ≫ δ) := hk₁.trans (hk₂.trans hj.symm)
  have heq : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (k ≫ δ) :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence.refl C.obj).isQCatEquivalence.ofFunctorIso hj.symm
  have hrd : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso r δ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.localizationProjectionComparisonOfTest δ
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberLocalizingEdges (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.essentialImage (IdentityLax.exactDiagonal C)))
    (IdentityLax.difference_isVerdier C).quotient k heq r
    ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.inverts_iff_kills_inclusion (IdentityLax.exactDiagonal C) re).mpr hzero) htest
  have hout : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (e.hom ≫ r ≫ y.hom) ((e.hom ≫ δ) ≫ y.hom) := by
    simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso, Category.assoc] using (hrd.precomp e.hom).postcomp y.hom
  have hcancel₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (e.hom ≫ r ≫ y.hom) (f ≫ y.inv ≫ y.hom) := by
    simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso, r, Category.assoc, Category.id_comp] using
      e.homInvIso.postcomp (f ≫ y.inv ≫ y.hom)
  have hcancel₂ : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (f ≫ y.inv ≫ y.hom) f := by
    simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso, Category.assoc, Category.comp_id] using y.invHomIso.precomp f
  exact hout.symm.trans (hcancel₁.trans hcancel₂)

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
