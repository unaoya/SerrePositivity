module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.CrystallineCover.Construction61Reflection
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Totalization.ComplexResolutionFunctor

/-!
# 元の射を指定半自由模型の結晶被覆で検出する

## 概要
元の完備複体間の射を、HT02 の指定半自由分解関手で計算した被覆像で検出する。

## 方針
元の増大の自然性と擬同型性で、既存の半自由模型上の反映を元の射へ戻す。

## 規約
元の source・target の p・d 完備性と、元の Construction 6.1 の前提を明示する。
元の複体の K-flat 性は仮定しない。

## 使われ方
元の affine line の標準 η の実現を、具体的な結晶被覆上の比較で検出する。
-/

public noncomputable section
universe u
open CategoryTheory
namespace SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
open DifferentialGraded DerivedCompletion InfinityCategories HTComparisonResolution
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] (P : OrientedPrism p A)
variable {K L : CochainComplex (ModuleCat.{u} A) ℤ}

/-- 元の完備な射は、指定半自由分解の結晶被覆像の擬同型性から検出できる。 -/
theorem quasiIso_of_resolvedCover_map_quasiIso
    (hF : IsCompletelyFlat (Ideal.span {Construction61.coverModPGenerator P})
      (baseChangeScalarModule (modPMap p P.deltaStructure.frobeniusLift)))
    (hR : IsSMulRegular (A ⧸ P.ideal) (p : A ⧸ P.ideal)) (f : K ⟶ L)
    (hpK : IsComplete A (p : A) (DerivedCategory.Q.obj K))
    (hpL : IsComplete A (p : A) (DerivedCategory.Q.obj L))
    (hdK : IsComplete A P.generator (DerivedCategory.Q.obj K))
    (hdL : IsComplete A P.generator (DerivedCategory.Q.obj L))
    (hf : QuasiIso ((Construction61.completedCoverModelFunctor P).map
      ((complexResolutionFunctor A).map f))) : QuasiIso f := by
  let S := complexResolutionFunctor A
  let ε := complexResolutionAugmentation A
  haveI := complexResolutionAugmentation_quasiIso A K
  haveI := complexResolutionAugmentation_quasiIso A L
  let eK := asIso (DerivedCategory.Q.map (ε.app K))
  let eL := asIso (DerivedCategory.Q.map (ε.app L))
  haveI : QuasiIso (S.map f) :=
    Construction61.quasiIso_of_completedCover_semifree_map_quasiIso P hF hR (S.map f)
      (complexResolutionFunctor_semifree A K) (complexResolutionFunctor_semifree A L)
      (isComplete_of_iso A (p : A) eK.symm hpK)
      (isComplete_of_iso A (p : A) eL.symm hpL)
      (isComplete_of_iso A P.generator eK.symm hdK)
      (isComplete_of_iso A P.generator eL.symm hdL) hf
  have he : S.map f ≫ ε.app L = ε.app K ≫ f := ε.naturality f
  haveI : QuasiIso (ε.app K ≫ f) :=
    he ▸ (inferInstance : QuasiIso (S.map f ≫ ε.app L))
  exact quasiIso_of_comp_left (ε.app K) f

end SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
