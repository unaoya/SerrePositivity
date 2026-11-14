module
public import SerrePositivity.KST.SConstruction.DGGluingLeftAxisNerve
public import SerrePositivity.KST.SConstruction.PerfectDGFullyFaithful
public import SerrePositivity.KST.SConstruction.PerfectDGExtensionFactorization
public import SerrePositivity.KST.SConstruction.DGUniverseQuasiFullyFaithful
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ExactSequences.ComparisonModels.Size

/-! # 元の左軸包含の実 Perf 延長
概要：同じ (c,0,0) の左軸包含を実 Perf へ延長し、全 Hom 準同型と左射影比較を得る。
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
  (z : D) (hz : CategoryTheory.Limits.IsZero (ForgetEnrichment.of (Complex R) z))

/-- 元の実左軸包含の、同じ実 graph による Perf 延長。 -/
def perfectDGGluingLeftAxis :
    DGFunctor R (PerfectDGModule R C) (PerfectDGModule R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M)) :=
  perfectDGExtension R C (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) (dgGluingLeftAxis R C D M z hz)

/-- 同じ実 Perf 左軸包含は、全 Hom 複体で準同型を誘導する。 -/
lemma perfectDGGluingLeftAxis_homQuasiIso :
    HomQuasiIso (perfectDGGluingLeftAxis R C D M z hz) :=
  perfectDGExtension_homQuasiIso_of_homQuasiIso R C (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M)
    (dgGluingLeftAxis R C D M z hz) (dgGluingLeftAxis_homQuasiIso R C D M z hz)

/-- 同じ実 Perf 左軸包含の共通宇宙の nerve は実写像空間上で充満忠実。 -/
lemma perfectDGGluingLeftAxis_nerve_fullyFaithful :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveUniverseMap (perfectDGGluingLeftAxis R C D M z hz)) :=
  dgNerveUniverseMap_fullyFaithful_of_homQuasiIso _
    (perfectDGGluingLeftAxis_homQuasiIso R C D M z hz)

/-- 同じ Perf 左軸の実左射影は、元の合成・恒等比較を通って元の対象と同型。 -/
def perfectDGGluingLeftAxisRetractionAt (X : PerfectDGModule R C) :
    ForgetEnrichment.of (Complex R)
      (((perfectDGGluingLeftAxis R C D M z hz).comp
        (perfectDGExtension R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) C (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLeft R C D M))).obj X) ≅
    ForgetEnrichment.of (Complex R) X :=
  (perfectDGExtensionFactorizationAt R C (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) C
    (dgGluingLeftAxis R C D M z hz) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLeft R C D M) (DGFunctor.id C)
    (dgGluingLeftAxis_left R C D M z hz) X) ≪≫ (perfectDGExtensionIdentityAt R C X)

/-- 同じ Perf 左射影の指定比較は、全 Hom 複体上で自然。 -/
lemma perfectDGGluingLeftAxisRetractionAt_naturality (X Y : PerfectDGModule R C) :
    ((perfectDGGluingLeftAxis R C D M z hz).comp
      (perfectDGExtension R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) C (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLeft R C D M))).map X Y ≫
      eHomWhiskerLeft (Complex R)
        (ForgetEnrichment.of (Complex R)
          (((perfectDGGluingLeftAxis R C D M z hz).comp
            (perfectDGExtension R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) C
              (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLeft R C D M))).obj X))
        (perfectDGGluingLeftAxisRetractionAt R C D M z hz Y).hom =
    eHomWhiskerRight (Complex R) (perfectDGGluingLeftAxisRetractionAt R C D M z hz X).hom
      (ForgetEnrichment.of (Complex R) Y) := by
  exact (dgClosedComparison_comp (Complex R)
    (perfectDGExtensionFactorizationAt R C (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) C
      (dgGluingLeftAxis R C D M z hz) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLeft R C D M) (DGFunctor.id C)
      (dgGluingLeftAxis_left R C D M z hz) X).hom
    (perfectDGExtensionFactorizationAt R C (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) C
      (dgGluingLeftAxis R C D M z hz) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLeft R C D M) (DGFunctor.id C)
      (dgGluingLeftAxis_left R C D M z hz) Y).hom
    (perfectDGExtensionIdentityAt R C X).hom (perfectDGExtensionIdentityAt R C Y).hom
    _ _ (𝟙 _)
    (perfectDGExtensionFactorizationAt_naturality R C (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) C
      (dgGluingLeftAxis R C D M z hz) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLeft R C D M) (DGFunctor.id C)
      (dgGluingLeftAxis_left R C D M z hz) X Y)
    ((perfectDGExtensionIdentityAt_naturality R C X Y).trans
      (Category.id_comp _).symm)).trans (Category.id_comp _)

end SerrePositivity.KST.SConstruction
