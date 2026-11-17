module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Totalization.FiniteCompletionReflection
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence

/-!
# 有限反復完備化と本体の導来圏の関手

## 概要
既存の導来主元完備化を同じ順で合成し、複体の反復模型と比較する。

## 方針
本体の比較自然同型と三角関手性を、関手の合成で受け取る。

## 規約
新しい導来圏や一般の導来関手を構成しない。

## 使われ方
BS 著者版 Lemma 4.22 の、完備化を施した横切断の完全三角形。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory HomologicalComplex
open SerrePositivity.DifferentialGraded SerrePositivity.DerivedCompletion

namespace SerrePositivity.BhattScholze.Prismatic.HTComparisonTotal
attribute [local instance] HasDerivedCategory.standard
variable {R : Type u} [CommRing R]

/-- 本体の導来主元完備化の、同じ有限列に沿う合成。 -/
def finiteDerivedCompletionFunctor : {r : ℕ} → (Fin r → R) →
    (ConcreteDerivedCategory R ⥤ ConcreteDerivedCategory R)
  | 0, _ => 𝟭 _
  | r+1, x => finiteDerivedCompletionFunctor (Fin.init x) ⋙
      derivedComplexCompletionFunctor R (x (Fin.last r))

/-- 合成した関手のシフトとの可換性は、本体の可換性の合成である。 -/
instance finiteDerivedCompletionFunctor_commShift {r : ℕ} (x : Fin r → R) :
    (finiteDerivedCompletionFunctor x).CommShift ℤ := by
  induction r with
  | zero => change (𝟭 (ConcreteDerivedCategory R)).CommShift ℤ; infer_instance
  | succ r ih =>
    haveI := ih (Fin.init x)
    change (finiteDerivedCompletionFunctor (Fin.init x) ⋙
      derivedComplexCompletionFunctor R (x (Fin.last r))).CommShift ℤ
    infer_instance

/-- 合成した関手の三角関手性は、本体の三角関手性の合成である。 -/
instance finiteDerivedCompletionFunctor_isTriangulated {r : ℕ} (x : Fin r → R) :
    (finiteDerivedCompletionFunctor x).IsTriangulated := by
  induction r with
  | zero => change (𝟭 (ConcreteDerivedCategory R)).IsTriangulated; infer_instance
  | succ r ih =>
    haveI := ih (Fin.init x)
    change (finiteDerivedCompletionFunctor (Fin.init x) ⋙
      derivedComplexCompletionFunctor R (x (Fin.last r))).IsTriangulated
    infer_instance

/-- 導来圏の合成関手と、実際の複体の反復模型との比較。 -/
def finiteDerivedCompletionComparison : ∀ {r : ℕ} (x : Fin r → R),
    DerivedCategory.Q ⋙ finiteDerivedCompletionFunctor x ≅
      finiteCompletionFunctor x ⋙ DerivedCategory.Q
  | 0, _ => Functor.rightUnitor DerivedCategory.Q ≪≫ (Functor.leftUnitor DerivedCategory.Q).symm
  | r+1, x =>
    (Functor.associator DerivedCategory.Q (finiteDerivedCompletionFunctor (Fin.init x))
      (derivedComplexCompletionFunctor R (x (Fin.last r)))).symm ≪≫
    Functor.isoWhiskerRight (finiteDerivedCompletionComparison (Fin.init x))
      (derivedComplexCompletionFunctor R (x (Fin.last r))) ≪≫
    Functor.associator (finiteCompletionFunctor (Fin.init x)) DerivedCategory.Q
      (derivedComplexCompletionFunctor R (x (Fin.last r))) ≪≫
    Functor.isoWhiskerLeft (finiteCompletionFunctor (Fin.init x))
      (derivedComplexCompletionComparison R (x (Fin.last r))) ≪≫
    (Functor.associator (finiteCompletionFunctor (Fin.init x))
      (complexCompletionFunctor R (x (Fin.last r))) DerivedCategory.Q).symm

/-- 合成関手のホモロジーと、実際の複体模型のホモロジーとの自然同型。 -/
def finiteCompletionHomologyNatIso {r : ℕ} (x : Fin r → R) (q : ℤ) :
    (DerivedCategory.Q ⋙ finiteDerivedCompletionFunctor x) ⋙
        DerivedCategory.homologyFunctor (ModuleCat.{u} R) q ≅
      finiteCompletionFunctor x ⋙ homologyFunctor (ModuleCat.{u} R) (.up ℤ) q :=
  Functor.isoWhiskerRight (finiteDerivedCompletionComparison x)
      (DerivedCategory.homologyFunctor (ModuleCat.{u} R) q) ≪≫
    Functor.associator (finiteCompletionFunctor x) DerivedCategory.Q
      (DerivedCategory.homologyFunctor (ModuleCat.{u} R) q) ≪≫
    Functor.isoWhiskerLeft (finiteCompletionFunctor x)
      (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} R) q)

/-- 具体的な完備化後の指定次数の擬同型性は、同じ導来関手のホモロジーで判定できる。 -/
theorem finiteCompletion_quasiIsoAt_iff {r : ℕ} (x : Fin r → R) {K M : Complex R}
    (g : K ⟶ M) (q : ℤ) :
    QuasiIsoAt ((finiteCompletionFunctor x).map g) q ↔
      IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) q).map
        ((finiteDerivedCompletionFunctor x).map (DerivedCategory.Q.map g))) := by
  rw [quasiIsoAt_iff_isIso_homologyMap]
  exact (NatIso.isIso_map_iff (finiteCompletionHomologyNatIso x q) g).symm

end SerrePositivity.BhattScholze.Prismatic.HTComparisonTotal
