module
public import SerrePositivity.KST.SConstruction.DGStrictSquareQuotientGeneration
public import SerrePositivity.KST.SConstruction.DGRepresentableEndMorita

/-! # 元の標準対角商と同じ指定右対象 End の Perf 同値
概要：元の二生成条件から、同じ実商と同じ指定 End の Perf 同値を構成する。
方針：元の標準対角商の単一生成を、D の End 再構成と元の Yoneda 比較へ渡す。
規約：生成条件は明示入力。使われ方：K-10 c の具体的商 End 模型。
-/
@[expose] public section
noncomputable section
universe u v w z t
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits DifferentialGraded InfinityCategories
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] [Small.{u} D] (E : Type z) [DGCategory R E]
  (p : DGFunctor R C E) (q : DGFunctor R D E)
  {P : Type t} [DGCategory R P] (L : DGFunctor R P C) (G : DGFunctor R P D)
  (h : L.comp p = G.comp q) (zc : C)
  (hc : IsZero (ForgetEnrichment.of (Complex R) zc))
  (zd : D) (hd : IsZero (ForgetEnrichment.of (Complex R) zd)) (b : D)
local notation "I" => dgStrictSquareQuotientInput R C D E p q L G h zc hc b

/-- 元の生成条件の下で、同じ標準対角商と同じ指定右対象 End の実 Perf 同値。 -/
def dgStrictSquareQuotientPerfectEquivalence
    (hL : modulePerfectOver R C (Set.range L.obj) = modulePerfect R C)
    (hD : modulePerfectOver R D {b} = modulePerfect R D) :
    PerfectModuleCategory R (I).quotientObject ≌
      PerfectModuleCategory R (dgStrictSquareQuotientEnd R C D E p q L G h zc hc b) :=
  dgRepresentableEndPerfectEquivalence R (I).quotientObject ((I).projection.obj (I).point)
    (dgStrictSquareQuotient_perfectOver_point_eq R C D E p q L G h zc hc zd hd b hL hD)

end SerrePositivity.KST.SConstruction
