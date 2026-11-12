module
public import SerrePositivity.KST.SConstruction.DGOdotAlgebraRealization
public import SerrePositivity.KST.SConstruction.DGOdotGeneratorConditions
public import SerrePositivity.DifferentialGraded.Verdier.Derived
public import SerrePositivity.DifferentialGraded.Morita.Perfect

/-! # 実 ⊙ 代数から元の対角商への同じ Perf 延長
概要：代数の一対象圏から指定 End を通る元の商への実射を固定する。
方針：D の導来 graph 合成比較を主 Perf へ制限し、既存の二同値を移す。
規約：二つの実自由生成条件は明示入力。使われ方：元の ⊙ の Perf 商比較。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory DifferentialGraded InfinityCategories
variable (R : Type u) [CommRing R] (d : DGOdotInput R)
local notation "B" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraCategory R (dgOdotAlgebra R d)
local notation "I" => dgOdotQuotientInput R d
local notation "Q" => DGOdotQuotientEnd R d
local notation "T" => DGLaxQuotientEndInput.quotientObject (I)
local notation "F" => dgOdotAlgebraToEnd R d
local notation "G" => DGLaxQuotientEndInput.endInclusion (I)

/-- 実 ⊙ の右加群用圏から、同じ元の対角商への実 dg 射。 -/
def dgOdotAlgebraToQuotient : DGFunctor R (B) (T) := (F).comp (G)

/-- 二回の元の主 Perf 延長と、同じ合成射の一回延長の指定自然同型。 -/
def dgOdotAlgebraQuotientPerfectCompositionIso :
    quasiEquivalencePerfectExtension R (B) (Q) (F) ⋙
      quasiEquivalencePerfectExtension R (Q) (T) (G) ≅
        quasiEquivalencePerfectExtension R (B) (T) (dgOdotAlgebraToQuotient R d) :=
  Morita.perfectFunctorCompositionIso R (B) (Q) (T)
    (dgDerivedExtension R (B) (Q) (F)) (dgDerivedExtension R (Q) (T) (G))
    (fun _ h => dgDerivedExtension_perfect R (B) (Q) (F) h)
    (fun _ h => dgDerivedExtension_perfect R (Q) (T) (G) h) ≪≫
      Morita.perfectFunctorIso R (B) (T) _ _
        (fun _ h => dgDerivedExtension_perfect R (Q) (T) (G)
          (dgDerivedExtension_perfect R (B) (Q) (F) h))
        (fun _ h => dgDerivedExtension_perfect R (B) (T)
          (dgOdotAlgebraToQuotient R d) h)
        (derivedGraphExtensionCompositionIso R (B) (Q) (T) (F) (G))

/-- 同じ実自由生成条件の下で、元の ⊙ から商への射の主 Perf 延長自体が同値。 -/
lemma dgOdotAlgebraToQuotient_isMorita (hgen : DGOdotGeneratorConditions R d) :
    (quasiEquivalencePerfectExtension R (B) (T) (dgOdotAlgebraToQuotient R d)).IsEquivalence := by
  letI : (quasiEquivalencePerfectExtension R (B) (Q) (F)).IsEquivalence :=
    (quasiEquivalencePerfectEquivalence R (B) (Q) (F)
    (dgOdotAlgebraToEnd_quasiEquivalence R d)).isEquivalence_functor
  letI : (quasiEquivalencePerfectExtension R (Q) (T) (G)).IsEquivalence :=
    dgOdotEndInclusion_isMorita R d hgen
  exact Functor.isEquivalence_of_iso (dgOdotAlgebraQuotientPerfectCompositionIso R d)

/-- 順方向を元の一回延長に固定した、同じ実 ⊙ と元の商の Perf 同値。 -/
def dgOdotAlgebraQuotientPerfectEquivalence (hgen : DGOdotGeneratorConditions R d) :
    PerfectModuleCategory R (B) ≌ PerfectModuleCategory R (T) := by
  letI := dgOdotAlgebraToQuotient_isMorita R d hgen
  exact (quasiEquivalencePerfectExtension R (B) (T) (dgOdotAlgebraToQuotient R d)).asEquivalence

/-- 同じ元の ⊙ から商への射の実 dg Perf 延長も、二生成条件の下で準同値。 -/
lemma dgOdotAlgebraToQuotient_perfectDG_quasiEquivalence
    (hgen : DGOdotGeneratorConditions R d) :
    QuasiEquivalence (perfectDGExtension R (B) (T) (dgOdotAlgebraToQuotient R d)) := by
  letI := dgOdotAlgebraToQuotient_isMorita R d hgen
  exact perfectDGExtension_quasiEquivalence R (B) (T) (dgOdotAlgebraToQuotient R d)

end SerrePositivity.KST.SConstruction
