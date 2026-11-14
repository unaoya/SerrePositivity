module
public import SerrePositivity.KST.SConstruction.DGGluingRightAxisNerve
public import SerrePositivity.KST.SConstruction.PerfectDGFullyFaithful
public import SerrePositivity.KST.SConstruction.PerfectDGExtensionFactorization
public import SerrePositivity.KST.SConstruction.DGUniverseQuasiFullyFaithful
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ExactSequences.ComparisonModels.Size

/-! # 元の右軸包含の実 Perf 延長
概要：同じ (0,d,0) の右軸包含を実 Perf へ延長し、全 Hom 準同型と右射影比較を得る。
方針：元の Hom 鎖同型から Perf の全次数判定を使い、同じ切断を合成・恒等比較へ移す。
規約：Small Perf を仮定しない。使われ方：Perf(gluing) の右成分と商の生成元。
-/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] [Small.{u} D] (M : Bimodule R C D)
  (z : C) (hz : CategoryTheory.Limits.IsZero (ForgetEnrichment.of (Complex R) z))

/-- 元の実右軸包含の、同じ実 graph による Perf 延長。 -/
def perfectDGGluingRightAxis :
    DGFunctor R (PerfectDGModule R D) (PerfectDGModule R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M)) :=
  perfectDGExtension R D (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) (dgGluingRightAxis R C D M z hz)

/-- 同じ実 Perf 右軸包含は、全 Hom 複体で準同型を誘導する。 -/
lemma perfectDGGluingRightAxis_homQuasiIso :
    HomQuasiIso (perfectDGGluingRightAxis R C D M z hz) :=
  perfectDGExtension_homQuasiIso_of_homQuasiIso R D (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M)
    (dgGluingRightAxis R C D M z hz) (dgGluingRightAxis_homQuasiIso R C D M z hz)

/-- 同じ実 Perf 右軸包含の共通宇宙の nerve は実写像空間上で充満忠実。 -/
lemma perfectDGGluingRightAxis_nerve_fullyFaithful :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveUniverseMap (perfectDGGluingRightAxis R C D M z hz)) :=
  dgNerveUniverseMap_fullyFaithful_of_homQuasiIso _
    (perfectDGGluingRightAxis_homQuasiIso R C D M z hz)

/-- 同じ Perf 右軸の実右射影は、元の合成・恒等比較を通って元の対象と同型。 -/
def perfectDGGluingRightAxisRetractionAt (X : PerfectDGModule R D) :
    ForgetEnrichment.of (Complex R)
      (((perfectDGGluingRightAxis R C D M z hz).comp
        (perfectDGExtension R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) D (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRight R C D M))).obj X) ≅
    ForgetEnrichment.of (Complex R) X :=
  (perfectDGExtensionFactorizationAt R D (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) D
    (dgGluingRightAxis R C D M z hz) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRight R C D M) (DGFunctor.id D)
    (dgGluingRightAxis_right R C D M z hz) X) ≪≫ (perfectDGExtensionIdentityAt R D X)

/-- 同じ Perf 右射影の指定比較は、全 Hom 複体上で自然。 -/
lemma perfectDGGluingRightAxisRetractionAt_naturality (X Y : PerfectDGModule R D) :
    ((perfectDGGluingRightAxis R C D M z hz).comp
      (perfectDGExtension R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) D (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRight R C D M))).map X Y ≫
      eHomWhiskerLeft (Complex R)
        (ForgetEnrichment.of (Complex R)
          (((perfectDGGluingRightAxis R C D M z hz).comp
            (perfectDGExtension R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) D
              (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRight R C D M))).obj X))
        (perfectDGGluingRightAxisRetractionAt R C D M z hz Y).hom =
    eHomWhiskerRight (Complex R) (perfectDGGluingRightAxisRetractionAt R C D M z hz X).hom
      (ForgetEnrichment.of (Complex R) Y) := by
  exact (dgClosedComparison_comp (Complex R)
    (perfectDGExtensionFactorizationAt R D (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) D
      (dgGluingRightAxis R C D M z hz) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRight R C D M) (DGFunctor.id D)
      (dgGluingRightAxis_right R C D M z hz) X).hom
    (perfectDGExtensionFactorizationAt R D (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) D
      (dgGluingRightAxis R C D M z hz) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRight R C D M) (DGFunctor.id D)
      (dgGluingRightAxis_right R C D M z hz) Y).hom
    (perfectDGExtensionIdentityAt R D X).hom (perfectDGExtensionIdentityAt R D Y).hom
    _ _ (𝟙 _)
    (perfectDGExtensionFactorizationAt_naturality R D (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) D
      (dgGluingRightAxis R C D M z hz) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRight R C D M) (DGFunctor.id D)
      (dgGluingRightAxis_right R C D M z hz) X Y)
    ((perfectDGExtensionIdentityAt_naturality R D X Y).trans
      (Category.id_comp _).symm)).trans (Category.id_comp _)

end SerrePositivity.KST.SConstruction
