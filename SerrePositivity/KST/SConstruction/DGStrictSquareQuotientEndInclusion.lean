module
public import SerrePositivity.KST.SConstruction.DGStrictSquareQuotientGeneration
public import SerrePositivity.KST.SConstruction.DGEndInclusionPerfectGeneration
public import SerrePositivity.KST.SConstruction.PerfectDGMoritaEquivalence

/-! # 元の標準対角商の指定 End 包含の実 Morita 判定
概要：元の二生成条件から、元の End 包含の実 Perf 延長そのものを同値にする。
方針：同じ指定商対象の単一生成を、元の End 包含の生成判定へ渡す。
規約：生成条件は明示入力。使われ方：具体的商 End 模型の元の Morita 射。
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

include zd hd in
/-- 同じ標準対角商への元の指定 End 包含の実 Perf 延長は、二生成条件の下で圏同値。 -/
lemma dgStrictSquareQuotientEndInclusion_isMorita
    (hL : modulePerfectOver R C (Set.range L.obj) = modulePerfect R C)
    (hD : modulePerfectOver R D {b} = modulePerfect R D) :
    (quasiEquivalencePerfectExtension R (I).endObject (I).quotientObject
      (I).endInclusion).IsEquivalence :=
  dgEndInclusionPerfect_isEquivalence R (I).quotientObject ((I).projection.obj (I).point)
    (dgStrictSquareQuotient_perfectOver_point_eq R C D E p q L G h zc hc zd hd b hL hD)

/-- 順方向が同じ元の End 包含の実 Perf 延長である、具体的標準対角商の圏同値。 -/
def dgStrictSquareQuotientEndInclusionPerfectEquivalence
    (hL : modulePerfectOver R C (Set.range L.obj) = modulePerfect R C)
    (hD : modulePerfectOver R D {b} = modulePerfect R D) :
    PerfectModuleCategory R (I).endObject ≌ PerfectModuleCategory R (I).quotientObject := by
  let := dgStrictSquareQuotientEndInclusion_isMorita R C D E p q L G h
    zc hc zd hd b hL hD
  exact (quasiEquivalencePerfectExtension R (I).endObject (I).quotientObject
    (I).endInclusion).asEquivalence

include zd hd in
/-- 元の End 包含の実 dg Perf 延長も、同じ二生成条件の下で準同値となる。 -/
lemma dgStrictSquareQuotientEndInclusion_perfectDG_quasiEquivalence
    (hL : modulePerfectOver R C (Set.range L.obj) = modulePerfect R C)
    (hD : modulePerfectOver R D {b} = modulePerfect R D) :
    QuasiEquivalence (perfectDGExtension R (I).endObject (I).quotientObject
      (I).endInclusion) := by
  let := dgStrictSquareQuotientEndInclusion_isMorita R C D E p q L G h
    zc hc zd hd b hL hD
  exact perfectDGExtension_quasiEquivalence R (I).endObject (I).quotientObject
    (I).endInclusion

end SerrePositivity.KST.SConstruction
