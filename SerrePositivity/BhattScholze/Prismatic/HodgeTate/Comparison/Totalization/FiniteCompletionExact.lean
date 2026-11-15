module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Totalization.FiniteCompletionDerived
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import Mathlib.CategoryTheory.Triangulated.HomologicalFunctor

/-!
# 完備化を施した短完全列のホモロジー

## 概要
本体の導来反復完備化を完全三角形へ施し、第一項の二次数の消滅で第二射を判定する。

## 方針
Mathlib の導来圏のホモロジー長完全列と、具体的な複体模型との比較を使う。

## 規約
元の短完全列が複体全体で分裂するとは仮定しない。

## 使われ方
BS 著者版 Lemma 4.22 の、完備テンソル後の有限頭部への射影。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated HomologicalComplex
open SerrePositivity.DifferentialGraded SerrePositivity.DerivedCompletion

namespace SerrePositivity.BhattScholze.Prismatic.HTComparisonTotal
attribute [local instance] HasDerivedCategory.standard
variable {R : Type u} [CommRing R]

/-- 完全三角形の第一項の二次数が零なら、第二射の指定次数のホモロジーは同型。 -/
theorem derived_homology_mor2_isIso_of_left_zero
    (T : Triangle (ConcreteDerivedCategory R)) (hT : T ∈ distTriang (ConcreteDerivedCategory R))
    (q : ℤ) (hq : IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) q).obj T.obj₁))
    (hq1 : IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) (q+1)).obj T.obj₁)) :
    IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) q).map T.mor₂) := by
  let H := DerivedCategory.homologyFunctor (ModuleCat.{u} R) 0
  haveI : Mono ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) q).map T.mor₂) :=
    (H.homologySequence_exact₂ T hT q).mono_g (hq.eq_zero_of_src _)
  haveI : Epi ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) q).map T.mor₂) :=
    (H.homologySequence_exact₃ T hT q (q+1) rfl).epi_f (hq1.eq_zero_of_tgt _)
  exact isIso_of_mono_of_epi _

/-- 完備化を施した短完全列で、第一項の二次数が零なら第二射は指定次数で擬同型。 -/
theorem finiteCompletion_quasiIsoAt_g_of_left_zero {r : ℕ} (x : Fin r → R)
    (S : ShortComplex (Complex R)) (hS : S.ShortExact) (q : ℤ)
    (hq : IsZero (((finiteCompletionFunctor x).obj S.X₁).homology q))
    (hq1 : IsZero (((finiteCompletionFunctor x).obj S.X₁).homology (q+1))) :
    QuasiIsoAt ((finiteCompletionFunctor x).map S.g) q := by
  apply (finiteCompletion_quasiIsoAt_iff x S.g q).mpr
  let T := (finiteDerivedCompletionFunctor x).mapTriangle.obj (DerivedCategory.triangleOfSES hS)
  have hT : T ∈ distTriang (ConcreteDerivedCategory R) :=
    (finiteDerivedCompletionFunctor x).map_distinguished _ (DerivedCategory.triangleOfSES_distinguished hS)
  change IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) q).map T.mor₂)
  apply derived_homology_mor2_isIso_of_left_zero T hT q
  · exact hq.of_iso ((finiteCompletionHomologyNatIso x q).app S.X₁)
  · exact hq1.of_iso ((finiteCompletionHomologyNatIso x (q+1)).app S.X₁)

end SerrePositivity.BhattScholze.Prismatic.HTComparisonTotal
