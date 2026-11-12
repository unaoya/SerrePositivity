module

public import SerrePositivity.EInfinity.PowerOperation.EilenbergMacLaneHammockFunctor
public import SerrePositivity.EInfinity.SimplicialLocalization.RelativeHammockSourceComparison

/-!
# 実複体への相対関手の native スペクトル化

DAG XIII §2.2 の係数模型の補助。証明済みの相対関手を同じ hammock で移し、
元の全図式へ戻る指定 sourceIso を保つ。［一般∞］移動候補。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.EInfinity.PowerOperation
open CategoryTheory SSet
open SerrePositivity.EInfinity.SimplicialLocalization
open SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
variable (k : Type u) [CommRing k] {C : RelativeCategory.{u + 1}}
variable (F : LocalizerMorphism C.weakEquivalences (complexRelativeCategory k).weakEquivalences)

/-- 同じ相対複体関手から native Sp への実関手。 -/
def relativeComplexSpectrum : kanHammockNerve C ⟶ KST.Spectra.Sp.{u} :=
  relativeKanHammockNerve F ≫ eilenbergMacLaneHammockFunctor k

/-- 元の厳密な全図式への、同じ指定スペクトル化の sourceIso。 -/
def relativeComplexSpectrum_sourceIso :
    FunctorIso (hammockLocalizationNerveMap C ≫ relativeComplexSpectrum k F)
      (nerveMap F.functor ≫ complexRelativeSpectrumSource k) := by
  change FunctorIso (hammockLocalizationNerveMap C ≫
    (relativeKanHammockNerve F ≫ eilenbergMacLaneHammockFunctor k)) _
  rw [← Category.assoc, relativeKanHammockNerve_source]
  simpa only [Category.assoc, complexHammockSource] using
    FunctorIso.precomp (eilenbergMacLaneHammockFunctor_sourceIso k) (nerveMap F.functor)

end SerrePositivity.EInfinity.PowerOperation
