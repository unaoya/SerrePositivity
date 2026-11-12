module
public import SerrePositivity.KST.SConstruction.DGOdotPerfectComparison

/-! # 実 ⊙ の Perf native nerve と元の商 Perf の比較
概要：元の実 ⊙ から商への射が、その元の自由代表と native Perf 同値を保持する。
方針：実 dg Perf 準同値に D の nerve 比較を適用し、元の representable 比較も回収する。
規約：この比較は二生成条件を明示入力とする。使われ方：具体的商の冪等完備化への接続。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory DifferentialGraded InfinityCategories
variable (R : Type u) [CommRing R] (d : DGOdotInput R)
local notation "B" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraCategory R (dgOdotAlgebra R d)
local notation "I" => dgOdotQuotientInput R d
local notation "T" => DGLaxQuotientEndInput.quotientObject (I)
local notation "F" => dgOdotAlgebraToQuotient R d

/-- 実 ⊙ の元の自由代表の点は、同じ商内の元の (0,b,0) の像そのもの。 -/
lemma dgOdotAlgebraToQuotient_point :
    (F).obj (Opposite.op _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGAlgebraPoint.star) = (I).projection.obj (I).point := rfl

/-- 同じ射の導来延長は、元の自由代表を同じ指定商対象の representable へ写す。 -/
def dgOdotAlgebraQuotientRepresentableIso :
    (dgDerivedExtension R (B) (T) (F)).obj ((moduleToDerived R (B)).obj
      (ForgetEnrichment.of (Complex R) (representable R (Opposite.op _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGAlgebraPoint.star)))) ≅
    (moduleToDerived R (T)).obj (ForgetEnrichment.of (Complex R)
      (representable R ((I).projection.obj (I).point))) :=
  dgDerivedExtensionRepresentableIso R (B) (T) (F) (Opposite.op _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGAlgebraPoint.star)

/-- 二生成条件の下で、元の一回の実 Perf 延長の native nerve 自体が同値を与える。 -/
def dgOdotAlgebraQuotientPerfectNerveEquivalence (hgen : DGOdotGeneratorConditions R d) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (PerfectDGModule R (B)))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (PerfectDGModule R (T))) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuasiEquivalenceNerveEquivalence (perfectDGExtension R (B) (T) (F))
    (dgOdotAlgebraToQuotient_perfectDG_quasiEquivalence R d hgen)

end SerrePositivity.KST.SConstruction
