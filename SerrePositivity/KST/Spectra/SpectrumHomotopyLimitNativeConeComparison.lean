module

public import SerrePositivity.KST.Spectra.SpectrumHomotopyLimitReflectedFamilyEquivalence
public import SerrePositivity.InfinityCategories.HomotopyLimits.GeneralHomHolimComparison
public import SerrePositivity.InfinityCategories.HomotopyLimits.WeightedConeEndPrecomposition

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
open SerrePositivity.InfinityCategories SerrePositivity.InfinityCategories.HomotopyLimits
namespace SerrePositivity.KST.Spectra.OmegaSpectrum
local instance nativeConeComparisonSimplicialCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory
local instance nativeConeComparisonHomKan (X Y : OmegaSpectrum.{u}) :
    KanComplex (SimplicialCategory.sHom X Y) := mappingSpace_kanComplex X Y
variable {I : Type u} [SmallCategory I]
local instance nativeConeComparisonCoefficientKan (X : OmegaSpectrum.{u})
    (D : I ⥤ OmegaSpectrum.{u}) (i : I) :
    KanComplex ((simplicialHomDiagram D X ⋙ SSet.opFunctor).obj i) :=
  inferInstanceAs (KanComplex (mappingSpace X (D.obj i)).op)
local instance nativeConeComparisonEndKan (X : OmegaSpectrum.{u}) (D : I ⥤ OmegaSpectrum.{u}) :
    KanComplex (bousfieldKanHolim (simplicialHomDiagram D X ⋙ SSet.opFunctor)) :=
  bousfieldKanHolim_kanComplex _

/-- 反転 Hom のパラメータに、元の反転 end の切断点を添える射。 -/
def homotopyLimitReflectedPointParameter (D : I ⥤ OmegaSpectrum.{u}) (X : OmegaSpectrum.{u}) :
    (mappingSpace X (homotopyLimit D)).op ⟶
      bousfieldKanHolim (simplicialHomDiagram D (homotopyLimit D) ⋙ SSet.opFunctor) ⊗
        (mappingSpace X (homotopyLimit D)).op :=
  ParameterPoint.family (homotopyLimitReflectedEndPointMap D)
    (mappingSpace X (homotopyLimit D)).op

/-- 元の BF Hom の反転から、元の図式上の coherent な錐の切断空間への実際の比較族。 -/
def homotopyLimitNativeConeComparison (D : I ⥤ OmegaSpectrum.{u}) (X : OmegaSpectrum.{u}) :
    (SSet.uliftFunctor.{u + 1, u}).obj (mappingSpace X (homotopyLimit D)).op ⟶
      coherentConeSectionSpace (strictCoherentDiagram D) (coherentNerveVertex X) :=
  (SSet.uliftFunctor.{u + 1, u}).map (homotopyLimitReflectedEndFamily D X) ≫
    reflectedHomHolimConeComparison D X

/-- 元の BF Hom の反転から coherent な錐の切断空間への比較族はホモトピー同値。 -/
lemma homotopyLimitNativeConeComparison_homotopyEquivalence
    (D : I ⥤ OmegaSpectrum.{u}) (X : OmegaSpectrum.{u}) :
    IsSimplicialHomotopyEquivalence (homotopyLimitNativeConeComparison D X) :=
  (DoldKanComparison.ulift_homotopyEquivalence.{u, u + 1}
    (homotopyLimitReflectedEndFamily_homotopyEquivalence D X)).comp
      (reflectedHomHolimConeComparison_homotopyEquivalence D X)

/-- 元の比較族の全 Hom 評価は、元の反転 end の点に対する weighted な前合成。 -/
lemma homotopyLimitNativeConeComparison_uncurry
    (D : I ⥤ OmegaSpectrum.{u}) (X : OmegaSpectrum.{u}) :
    relativeFunctorUncurry (homotopyLimitNativeConeComparison D X) =
      ((SSet.uliftFunctor.{u + 1, u}).obj (nerve I) ◁
        (SSet.uliftFunctor.{u + 1, u}).map (homotopyLimitReflectedPointParameter D X)) ≫
        (uliftTensorIso (nerve I)
          (bousfieldKanHolim
            (simplicialHomDiagram D (homotopyLimit D) ⋙ SSet.opFunctor) ⊗
              (mappingSpace X (homotopyLimit D)).op)).inv ≫
          (SSet.uliftFunctor.{u + 1, u}).map
            ((α_ (nerve I)
              (bousfieldKanHolim (simplicialHomDiagram D (homotopyLimit D) ⋙ SSet.opFunctor))
              (mappingSpace X (homotopyLimit D)).op).inv ≫
              (bousfieldKanWeightedNerveEvaluation
                (simplicialHomDiagram D (homotopyLimit D) ⋙ SSet.opFunctor) ▷
                  (mappingSpace X (homotopyLimit D)).op)) ≫
            (uliftTensorIso _ _).hom ≫
              weightedCoslicePrecompositionFamily D X (homotopyLimit D) := by
  rw [homotopyLimitNativeConeComparison, homotopyLimitReflectedEndFamily,
    Functor.map_comp, Category.assoc, HomotopyLimits.relativeFunctorUncurry_parameter,
    reflectedHomHolimConeComparison_precomposition_uncurry,
    weightedCosliceEndPrecompositionEvaluation_eq_family]
  rfl

end SerrePositivity.KST.Spectra.OmegaSpectrum
