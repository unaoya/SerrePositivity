module

public import SerrePositivity.EInfinity.PowerOperation.EilenbergMacLaneComponents
public import SerrePositivity.EInfinity.PowerOperation.EilenbergMacLaneTruncationNaturality
public import SerrePositivity.EInfinity.PowerOperation.EilenbergMacLaneGammaAxes

/-!
# シフト零を介さない Γ の連結成分と H⁰ の自然な比較

DAG XIII §2.2 の零次数の Ω 比較への前段。元の Γ と正規化の同じ余単位を使う。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.PowerOperation
open CategoryTheory AlgebraicTopology HomologicalComplex
open SerrePositivity.DifferentialGraded
open SerrePositivity.InfinityCategories.Project.DerivedCategories
variable (A : Type u) [CommRing A]

/-- シフトを入れずに実 Γ へ送る単体的加群の全関手。 -/
def gammaModuleFunctor : Complex A ⥤ SimplicialObject (ModuleCat A) :=
  (ComplexShape.embeddingUpIntLE 0).truncLE'Functor (ModuleCat A) ⋙ Abelian.DoldKan.Γ

/-- 実 Γ の正規化余単位を、同じホモロジー関手へ送った全自然同型。 -/
def normalizedGammaHomologyIso (d : ℕ) :
    gammaModuleFunctor A ⋙ Abelian.DoldKan.N ⋙
        homologyFunctor (ModuleCat A) (.down ℕ) d ≅
      (ComplexShape.embeddingUpIntLE 0).truncLE'Functor (ModuleCat A) ⋙
        homologyFunctor (ModuleCat A) (.down ℕ) d :=
  Functor.isoWhiskerRight
    (Functor.isoWhiskerLeft
      ((ComplexShape.embeddingUpIntLE 0).truncLE'Functor (ModuleCat A))
      (Abelian.DoldKan.equivalence : SimplicialObject (ModuleCat A) ≌
        ChainComplex (ModuleCat A) ℕ).counitIso)
    (homologyFunctor (ModuleCat A) (.down ℕ) d)

/-- Γ の成分を、同じ smart 切断の H₀ と比較する。 -/
def gammaPiZeroTruncationEquiv (M : Complex A) :
    SSet.π₀ ((ComplexLimits.truncatedDoldKanFunctor A).obj M) ≃
      (M.truncLE' (ComplexShape.embeddingUpIntLE 0)).homology 0 :=
  (modulePiZeroMooreEquiv (gammaModule A M)).trans
    ((normalizedGammaHomologyIso A 0).app M).toLinearEquiv.toEquiv

lemma gammaPiZeroTruncationEquiv_naturality {M N : Complex A} (f : M ⟶ N)
    (a : SSet.π₀ ((ComplexLimits.truncatedDoldKanFunctor A).obj M)) :
    gammaPiZeroTruncationEquiv A N
      (SSet.mapπ₀ ((ComplexLimits.truncatedDoldKanFunctor A).map f) a) =
      (homologyMap (truncLE'Map f (ComplexShape.embeddingUpIntLE 0)) 0).hom
        (gammaPiZeroTruncationEquiv A M a) := by
  change ((normalizedGammaHomologyIso A 0).app N).hom.hom
    (modulePiZeroMooreEquiv (gammaModule A N)
      (SSet.mapπ₀ (moduleUnderlyingSSetMap ((gammaModuleFunctor A).map f)) a)) = _
  rw [modulePiZeroMooreEquiv_naturality]
  exact congrArg (fun g => g.hom (modulePiZeroMooreEquiv (gammaModule A M) a))
    ((normalizedGammaHomologyIso A 0).hom.naturality f)

/-- 元の Γ の成分は、元の複体の H⁰ と全単射で対応する。 -/
def gammaPiZeroCohomologyEquiv (M : Complex A) :
    SSet.π₀ ((ComplexLimits.truncatedDoldKanFunctor A).obj M) ≃ M.homology 0 :=
  (gammaPiZeroTruncationEquiv A M).trans
    ((smartTruncationHomologyIso A M 0) ≪≫
      (show M.homology (-(0 : ℤ)) ≅ M.homology 0 from Iso.refl _)).toLinearEquiv.toEquiv

lemma gammaPiZeroCohomologyEquiv_naturality {M N : Complex A} (f : M ⟶ N)
    (a : SSet.π₀ ((ComplexLimits.truncatedDoldKanFunctor A).obj M)) :
    gammaPiZeroCohomologyEquiv A N
      (SSet.mapπ₀ ((ComplexLimits.truncatedDoldKanFunctor A).map f) a) =
      (homologyMap f 0).hom (gammaPiZeroCohomologyEquiv A M a) := by
  change (smartTruncationHomologyIso A N 0).hom.hom
    (gammaPiZeroTruncationEquiv A N
      (SSet.mapπ₀ ((ComplexLimits.truncatedDoldKanFunctor A).map f) a)) = _
  rw [gammaPiZeroTruncationEquiv_naturality]
  exact congrArg (fun k => k.hom (gammaPiZeroTruncationEquiv A M a))
    (smartTruncationHomologyIso_naturality f 0)

end SerrePositivity.EInfinity.PowerOperation
