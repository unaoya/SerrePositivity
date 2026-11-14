module
public import SerrePositivity.KST.SConstruction.DGOdotRightAlgebraComparison
public import SerrePositivity.KST.SConstruction.DGOdotPerfectComparison
public import SerrePositivity.KST.SConstruction.PerfectDGExtensionFactorization
public import SerrePositivity.DifferentialGraded.Functor.DGClosedComparisonIso

/-! # 元の右代数射から同じ実商への厳密因子分解と Perf 比較
概要：右代数から ⊙ を経由する射を、元の右 End 射と商包含の合成へ照合する。
方針：元の厳密等式に、同じ実 Perf 延長の全 Hom 自然な因子分解比較を適用する。
規約：元の代数射・指定商を保持。使われ方：LT の右辺と実商図式の接続。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory DifferentialGraded InfinityCategories
variable (R : Type u) [CommRing R] (d : DGOdotInput R)
local notation "D" => _root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.dgAlgebraCategory R (DGOdotInput.right d)
local notation "B" => _root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.dgAlgebraCategory R (dgOdotAlgebra R d)
local notation "I" => dgOdotQuotientInput R d
local notation "T" => DGLaxQuotientEndInput.quotientObject (I)
local notation "F" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraMap R (dgOdotRightMap R d)
local notation "G" => dgOdotAlgebraToQuotient R d

/-- 元の右代数の全 Hom を、元の右 End 射と指定商包含へ送る実射。 -/
def dgOdotOriginalRightToQuotient : DGFunctor R (D) (T) :=
  ((dgAlgebraToOriginalEnd R d.right).comp (dgOdotRightEndMap R d)).comp (I).endInclusion

/-- 右代数から ⊙ を経由する実射は、元の右 End 射の商への像を厳密に回収する。 -/
lemma dgOdotRightMap_toQuotient :
    (F).comp (G) = dgOdotOriginalRightToQuotient R d :=
  (strictDGFunctor_comp_assoc (F) (dgOdotAlgebraToEnd R d) (I).endInclusion).symm.trans
    (congrArg (fun H => H.comp (I).endInclusion) (dgOdotRightMap_toEnd R d))

/-- 元の右代数射を ⊙ と商へ二回延長することと、元の商射の一回延長の指定同型。 -/
def dgOdotRightQuotientPerfectAt (X : PerfectDGModule R (D)) :
    ForgetEnrichment.of (Complex R)
      (((perfectDGExtension R (D) (B) (F)).comp
        (perfectDGExtension R (B) (T) (G))).obj X) ≅
    ForgetEnrichment.of (Complex R)
      ((perfectDGExtension R (D) (T) (dgOdotOriginalRightToQuotient R d)).obj X) :=
  perfectDGExtensionFactorizationAt R (D) (B) (T) (F) (G)
    (dgOdotOriginalRightToQuotient R d) (dgOdotRightMap_toQuotient R d) X

/-- 同じ元の実 Perf 比較は、全 Hom 複体上で自然。 -/
lemma dgOdotRightQuotientPerfectAt_naturality (X Y : PerfectDGModule R (D)) :
    ((perfectDGExtension R (D) (B) (F)).comp (perfectDGExtension R (B) (T) (G))).map X Y ≫
      eHomWhiskerLeft (Complex R) _ (dgOdotRightQuotientPerfectAt R d Y).hom =
    (perfectDGExtension R (D) (T) (dgOdotOriginalRightToQuotient R d)).map X Y ≫
      eHomWhiskerRight (Complex R) (dgOdotRightQuotientPerfectAt R d X).hom _ :=
  perfectDGExtensionFactorizationAt_naturality R (D) (B) (T) (F) (G)
    (dgOdotOriginalRightToQuotient R d) (dgOdotRightMap_toQuotient R d) X Y

/-- 元の成分と全 Hom 自然性を保持する、同じ閉零 Perf 関手間の自然同型。 -/
def dgOdotRightQuotientPerfectClosedIso :
    ((perfectDGExtension R (D) (B) (F)).comp (perfectDGExtension R (B) (T) (G))).onClosed ≅
      (perfectDGExtension R (D) (T) (dgOdotOriginalRightToQuotient R d)).onClosed :=
  dgFunctorClosedComparisonIso R _ _ (dgOdotRightQuotientPerfectAt R d)
    (dgOdotRightQuotientPerfectAt_naturality R d)

end SerrePositivity.KST.SConstruction
