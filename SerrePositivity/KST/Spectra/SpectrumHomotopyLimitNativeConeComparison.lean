module

public import SerrePositivity.KST.Spectra.SpectrumHomotopyLimitReflectedFamilyEquivalence
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.GeneralHomHolimComparison
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.WeightedCones.WeightedConeEndPrecomposition

/-!
概要：元の反転 end の点の全 Hom 比較を coherent な錐の切断空間へ送り、その同値性を示す。
方針：反転比較族の同値と共有の一般形状の切断比較の同値を合成し、普遍評価で式を計算する。
規約：元の図式の切断へ向かう比較そのものを保持する。使われ方：coherent 錐全体の制限との一致。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Spectra.OmegaSpectrum
local instance nativeConeComparisonSimplicialCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory
local instance nativeConeComparisonHomKan (X Y : OmegaSpectrum.{u}) :
    KanComplex (SimplicialCategory.sHom X Y) := mappingSpace_kanComplex X Y
variable {I : Type u} [SmallCategory I]
local instance nativeConeComparisonCoefficientKan (X : OmegaSpectrum.{u})
    (D : I ⥤ OmegaSpectrum.{u}) (i : I) :
    KanComplex ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram D X ⋙ SSet.opFunctor).obj i) :=
  inferInstanceAs (KanComplex (mappingSpace X (D.obj i)).op)
local instance nativeConeComparisonEndKan (X : OmegaSpectrum.{u}) (D : I ⥤ OmegaSpectrum.{u}) :
    KanComplex (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanHolim (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram D X ⋙ SSet.opFunctor)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanHolim_kanComplex _

/-- 反転 Hom のパラメータに、元の反転 end の切断点を添える射。 -/
def homotopyLimitReflectedPointParameter (D : I ⥤ OmegaSpectrum.{u}) (X : OmegaSpectrum.{u}) :
    (mappingSpace X (homotopyLimit D)).op ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanHolim (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram D (homotopyLimit D) ⋙ SSet.opFunctor) ⊗
        (mappingSpace X (homotopyLimit D)).op :=
  _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.family (homotopyLimitReflectedEndPointMap D)
    (mappingSpace X (homotopyLimit D)).op

/-- 元の BF Hom の反転から、元の図式上の coherent な錐の切断空間への実際の比較族。 -/
def homotopyLimitNativeConeComparison (D : I ⥤ OmegaSpectrum.{u}) (X : OmegaSpectrum.{u}) :
    (SSet.uliftFunctor.{u + 1, u}).obj (mappingSpace X (homotopyLimit D)).op ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.coherentConeSectionSpace (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram D) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex X) :=
  (SSet.uliftFunctor.{u + 1, u}).map (homotopyLimitReflectedEndFamily D X) ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.reflectedHomHolimConeComparison D X

/-- 元の BF Hom の反転から coherent な錐の切断空間への比較族はホモトピー同値。 -/
lemma homotopyLimitNativeConeComparison_homotopyEquivalence
    (D : I ⥤ OmegaSpectrum.{u}) (X : OmegaSpectrum.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (homotopyLimitNativeConeComparison D X) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.ulift_homotopyEquivalence.{u, u + 1}
    (homotopyLimitReflectedEndFamily_homotopyEquivalence D X)).comp
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.reflectedHomHolimConeComparison_homotopyEquivalence D X)

/-- 元の比較族の全 Hom 評価は、元の反転 end の点に対する weighted な前合成。 -/
lemma homotopyLimitNativeConeComparison_uncurry
    (D : I ⥤ OmegaSpectrum.{u}) (X : OmegaSpectrum.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry (homotopyLimitNativeConeComparison D X) =
      ((SSet.uliftFunctor.{u + 1, u}).obj (nerve I) ◁
        (SSet.uliftFunctor.{u + 1, u}).map (homotopyLimitReflectedPointParameter D X)) ≫
        (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftTensorIso (nerve I)
          (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanHolim
            (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram D (homotopyLimit D) ⋙ SSet.opFunctor) ⊗
              (mappingSpace X (homotopyLimit D)).op)).inv ≫
          (SSet.uliftFunctor.{u + 1, u}).map
            ((α_ (nerve I)
              (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanHolim (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram D (homotopyLimit D) ⋙ SSet.opFunctor))
              (mappingSpace X (homotopyLimit D)).op).inv ≫
              (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeightedNerveEvaluation
                (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram D (homotopyLimit D) ⋙ SSet.opFunctor) ▷
                  (mappingSpace X (homotopyLimit D)).op)) ≫
            (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftTensorIso _ _).hom ≫
              _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedCoslicePrecompositionFamily D X (homotopyLimit D) := by
  rw [homotopyLimitNativeConeComparison, homotopyLimitReflectedEndFamily,
    Functor.map_comp, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.relativeFunctorUncurry_parameter,
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.reflectedHomHolimConeComparison_precomposition_uncurry,
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedCosliceEndPrecompositionEvaluation_eq_family]
  rfl

end SerrePositivity.KST.Spectra.OmegaSpectrum
