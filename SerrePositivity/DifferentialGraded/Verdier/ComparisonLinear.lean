module
public import SerrePositivity.DifferentialGraded.Quotient.DerivedComparisonCanonical
public import SerrePositivity.DifferentialGraded.Quotient.DerivedComparisonPerfect
public import SerrePositivity.DifferentialGraded.Derived.HomotopyLinear

/-! # 局所 dg 商・perfect 比較の係数環上の線形性

既存の比較関手の定義と自然同型を使い、U17c の正方形の全辺に線形性を与える。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Functor Idempotents
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

instance derivedFiniteCellInclusionLinear (S : Set D) :
    (derivedFiniteCellInclusion A D S).Linear A where
  map_smul _ _ := rfl

instance homotopyFiniteCellToDerivedLinear (S : Set D) :
    (homotopyFiniteCellToDerived A D S).Linear A := by
  dsimp [homotopyFiniteCellToDerived]
  infer_instance
instance homotopyFiniteCellToTriaLinear (S : Set D) :
    (homotopyFiniteCellToTria A D S).Linear A where
  map_smul f r := by
    apply (derivedFiniteCellInclusion A D S).map_injective
    exact (homotopyFiniteCellToDerived A D S).map_smul r f
instance homotopyFiniteCellTriaEquivalenceFunctorLinear (S : Set D) :
    (homotopyFiniteCellTriaEquivalence A D S).functor.Linear A :=
  homotopyFiniteCellToTriaLinear A D S

instance moduleDerivedKaroubiEquivalenceFunctorLinear :
    (moduleDerivedKaroubiEquivalence A D).functor.Linear A := by
  change (toKaroubi (DerivedModuleCategory A D)).Linear A
  infer_instance
instance finiteCellKaroubiFunctorLinear (S : Set D) :
    (finiteCellKaroubiFunctor A D S).Linear A := by
  dsimp [finiteCellKaroubiFunctor]
  infer_instance
instance finiteCellKaroubiRealizationLinear (S : Set D) :
    (finiteCellKaroubiRealization A D S).Linear A := by
  dsimp [finiteCellKaroubiRealization]
  infer_instance
instance finiteCellKaroubiToPerfectLinear (S : Set D) :
    (finiteCellKaroubiToPerfect A D S).Linear A where
  map_smul f r := by
    apply (modulePerfectOver A D S).ι.map_injective
    exact (finiteCellKaroubiRealization A D S).map_smul r f
instance finiteCellKaroubiPerfectEquivalenceFunctorLinear (S : Set D) :
    (finiteCellKaroubiPerfectEquivalence A D S).functor.Linear A :=
  finiteCellKaroubiToPerfectLinear A D S

namespace DGQuotient
instance quotientCellToDerivedLinear (S : Set D) :
    (quotientCellToDerived A D S).Linear A := by
  dsimp [quotientCellToDerived]
  infer_instance
instance quotientTriaToDerivedLinear (S : Set D) :
    (quotientTriaToDerived A D S).Linear A := by
  dsimp [quotientTriaToDerived]
  infer_instance
instance quotientTriaFunctorLinear (S : Set D) :
    (quotientTriaFunctor A D S).Linear A where
  map_smul f r := by
    apply (triaInclusion A (QuotientObject D S)).map_injective
    exact (quotientTriaToDerived A D S).map_smul r f
instance quotientVerdierComparisonLinear (S : Set D) :
    (quotientVerdierComparison A D S).Linear A :=
  (Localization.functor_linear_iff (triaQuotient A D S) (triaImage A D S).trW A
    (quotientTriaFunctor A D S) (quotientVerdierComparison A D S)).mp inferInstance
instance localQuotientTriaFunctorLinear (S : Set D) :
    (localQuotientTriaFunctor A D S).Linear A :=
  Functor.linear_of_iso A (quotientComparisonModelsIso A D S).symm
instance localQuotientTriaEquivalenceFunctorLinear (S : Set D) (h : localKFlat A D S) :
    (localQuotientTriaEquivalence A D S h).functor.Linear A := by
  change (localQuotientTriaFunctor A D S).Linear A
  infer_instance
instance localCompletedQuotientEquivalenceFunctorLinear (S : Set D) (h : localKFlat A D S) :
    (localCompletedQuotientEquivalence A D S h).functor.Linear A := by
  change ((functorExtension₂ _ _).obj (localQuotientTriaEquivalence A D S h).functor).Linear A
  infer_instance
instance localPerfectQuotientEquivalenceFunctorLinear (S : Set D) (h : localKFlat A D S) :
    (localPerfectQuotientEquivalence A D S h).functor.Linear A := by
  dsimp [localPerfectQuotientEquivalence]
  infer_instance
instance localSmallPerfectQuotientEquivalenceFunctorLinear (S : Set D) (h : localKFlat A D S) :
    (localSmallPerfectQuotientEquivalence A D S h).functor.Linear A := by
  dsimp [localSmallPerfectQuotientEquivalence]
  infer_instance
instance localPerfectKaroubiFirstEquivalenceFunctorLinear (S : Set D) (h : localKFlat A D S) :
    (localPerfectKaroubiFirstEquivalence A D S h).functor.Linear A := by
  dsimp [localPerfectKaroubiFirstEquivalence]
  infer_instance
end DGQuotient
end SerrePositivity.DifferentialGraded
