module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Totalization.FiniteCompletionDerived
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Totalization.ResolvedScalarExtension
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.Restriction.Completion

/-!
# 固定係数模型と指定した S 線形底変換模型

## 概要
任意の入力の指定 K-flat 分解上の S 線形底変換を、固定した R 線形係数模型と比較する。

## 方針
分解の射と係数増大の擬同型を導来圏で反転し、既存の係数制限と完備化の自然同型を使う。

## 規約
入力自体の K-flat 性は要求しない。分解を無断で図式へ束ねず、係数分解に S 作用を与えない。

## 使われ方
BS 著者版 Lemma 4.22 の、標準 S 線形底変換の指定模型への接続。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory HomologicalComplex
open SerrePositivity.DifferentialGraded SerrePositivity.DerivedCompletion

namespace SerrePositivity.BhattScholze.Prismatic.HTComparisonTotal
attribute [local instance] HasDerivedCategory.standard
variable {R S : Type u} [CommRing R] [CommRing S]

/-- 係数制限と同じ有限列の導来反復完備化の自然な交換。 -/
def finiteDerivedCompletionRestrictionIso (f : R →+* S) :
    ∀ {r : ℕ} (x : Fin r → R),
    derivedRestrictScalars f ⋙ finiteDerivedCompletionFunctor x ≅
      finiteDerivedCompletionFunctor (fun j => f (x j)) ⋙ derivedRestrictScalars f
  | 0, _ => Functor.rightUnitor (derivedRestrictScalars f) ≪≫
      (Functor.leftUnitor (derivedRestrictScalars f)).symm
  | r+1, x =>
    (Functor.associator (derivedRestrictScalars f)
      (finiteDerivedCompletionFunctor (Fin.init x))
      (derivedComplexCompletionFunctor R (x (Fin.last r)))).symm ≪≫
    Functor.isoWhiskerRight (finiteDerivedCompletionRestrictionIso f (Fin.init x))
      (derivedComplexCompletionFunctor R (x (Fin.last r))) ≪≫
    Functor.associator (finiteDerivedCompletionFunctor (fun j => f (Fin.init x j)))
      (derivedRestrictScalars f) (derivedComplexCompletionFunctor R (x (Fin.last r))) ≪≫
    Functor.isoWhiskerLeft (finiteDerivedCompletionFunctor (fun j => f (Fin.init x j)))
      (derivedCompletionRestrictionIso f (x (Fin.last r))) ≪≫
    (Functor.associator (finiteDerivedCompletionFunctor (fun j => f (Fin.init x j)))
      (derivedComplexCompletionFunctor S (f (x (Fin.last r)))) (derivedRestrictScalars f)).symm

namespace ScalarResolution
variable {f : R →+* S} (L : ScalarResolution f)

/-- 任意の入力の指定 K-flat 分解で計算した実際の S 底変換への模型同型。 -/
def baseChangeModelIso {P K : Complex R} (q : P ⟶ K) (hq : QuasiIso q)
    (hP : complexKFlat R P) :
    DerivedCategory.Q.obj (L.tensorFunctor.obj K) ≅
      (derivedRestrictScalars f).obj (DerivedCategory.Q.obj (baseChange f P)) := by
  haveI := hq
  haveI := L.tensorFunctor_map_quasiIso q
  haveI := L.comparison_quasiIso P hP
  exact (asIso (DerivedCategory.Q.map (L.tensorFunctor.map q))).symm ≪≫
    asIso (DerivedCategory.Q.map (L.comparison P)) ≪≫
    ((derivedRestrictScalarsFactors f).app (baseChange f P)).symm

/-- 同じ指定 S 線形底変換の有限列の完備化と、固定 R 模型の反復完備化との同型。 -/
def finiteCompletedBaseChangeModelIso {r : ℕ} (x : Fin r → R)
    {P K : Complex R} (q : P ⟶ K) (hq : QuasiIso q) (hP : complexKFlat R P) :
    DerivedCategory.Q.obj ((finiteCompletionFunctor x).obj (L.tensorFunctor.obj K)) ≅
      (derivedRestrictScalars f).obj
        ((finiteDerivedCompletionFunctor (fun j => f (x j))).obj
          (DerivedCategory.Q.obj (baseChange f P))) :=
  ((finiteDerivedCompletionComparison x).app (L.tensorFunctor.obj K)).symm ≪≫
    (finiteDerivedCompletionFunctor x).mapIso (L.baseChangeModelIso q hq hP) ≪≫
    (finiteDerivedCompletionRestrictionIso f x).app (DerivedCategory.Q.obj (baseChange f P))

/-- 全ての非有界入力で、上の指定模型の入力が実際に存在する。 -/
theorem exists_baseChangeModel (K : Complex R) :
    ∃ (P : Complex R) (q : P ⟶ K), QuasiIso q ∧ complexKFlat R P := by
  obtain ⟨P, q, _, hq, _, hP, _⟩ := exists_unbounded_baseChange_model (RingHom.id R) K
  exact ⟨P, q, hq, hP⟩

end ScalarResolution
end SerrePositivity.BhattScholze.Prismatic.HTComparisonTotal
