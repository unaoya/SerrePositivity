module
public import SerrePositivity.DifferentialGraded.Morita.PerfectQuasiEquivalenceTriangles

/-! # 元の指定 End 包含の実 Perf 延長の充満忠実性
概要：元の全 End 包含の実導来延長と、その実 Perf 制限の全 Hom を保持する。
方針：包含の Hom が恒等射であることを D の導来延長の充満忠実性へ渡す。
規約：生成性はまだ要求しない。使われ方：同じ対角商の指定 End の Morita 判定。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory HomologicalComplex DifferentialGraded
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  (b : D)
local notation "F" => endomorphismInclusion R b
local notation "T" => dgDerivedExtension R (EndomorphismObject b) D (F)
local instance : (perfectModuleInclusion R (EndomorphismObject b) Set.univ).Full :=
  inferInstanceAs ((modulePerfect R (EndomorphismObject b)).ι.Full)
local instance : (perfectModuleInclusion R (EndomorphismObject b) Set.univ).Faithful :=
  inferInstanceAs ((modulePerfect R (EndomorphismObject b)).ι.Faithful)

omit [Small.{u} D] in
/-- 元の全 End 包含は各 Hom 複体で恒等射を持つ。 -/
lemma dgEndInclusion_homQuasiIso : HomQuasiIso (F) := by
  intro x y
  change QuasiIso (𝟙 _)
  constructor
  intro n
  exact quasiIsoAt_of_isIso (𝟙 _) n

/-- 元の全 End 包含に沿う実導来延長は充満忠実。 -/
def dgEndInclusionDerivedFullyFaithful : (T).FullyFaithful :=
  dgDerivedExtensionFullyFaithful R (EndomorphismObject b) D (F)
    (dgEndInclusion_homQuasiIso R D b)

/-- 元の全 End 包含に沿う実 Perf 延長は充満忠実。 -/
def dgEndInclusionPerfectFullyFaithful :
    (quasiEquivalencePerfectExtension R (EndomorphismObject b) D (F)).FullyFaithful := by
  let : (perfectModuleInclusion R D Set.univ).Faithful :=
    inferInstanceAs ((modulePerfect R D).ι.Faithful)
  let h := (Functor.FullyFaithful.ofFullyFaithful
    (perfectModuleInclusion R (EndomorphismObject b) Set.univ)).comp
      (dgEndInclusionDerivedFullyFaithful R D b)
  exact Functor.FullyFaithful.ofCompFaithful (h.ofIso
    (quasiEquivalencePerfectExtensionInclusionIso R (EndomorphismObject b) D (F)).symm)


end SerrePositivity.KST.SConstruction
