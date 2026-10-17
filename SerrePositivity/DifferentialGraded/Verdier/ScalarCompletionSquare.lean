module
public import SerrePositivity.DifferentialGraded.Verdier.GraphPerfectSquare

/-! # 係数変更の tria 完備化と既存の perfect 比較による構成の一致 -/
@[expose] public section
noncomputable section
set_option synthInstance.maxSize 1024
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory CategoryTheory.Functor Idempotents ScalarExtension
variable {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')
  (D : Type v) [DGCategory A D] [Small.{u} D] (S : Set D)
  (h : localKFlat A D S) (h' : localKFlat A' (DGBaseChange φ D) S)

/-- 未完備の指定商上の係数変更を、元の Karoubi 関手延長で完備化する。 -/
def scalarCompletedTriaFunctor :
    CompletedTriaQuotient A D S ⥤ CompletedTriaQuotient A' (DGBaseChange φ D) S :=
  (functorExtension₂ _ _).obj (localScalarTriaExtension φ S h h')

instance scalarCompletedTriaFunctorCommShift :
    (scalarCompletedTriaFunctor φ D S h h').CommShift ℤ := by
  dsimp [scalarCompletedTriaFunctor]
  infer_instance
instance scalarCompletedTriaFunctorIsTriangulated :
    (scalarCompletedTriaFunctor φ D S h h').IsTriangulated := by
  dsimp [scalarCompletedTriaFunctor]
  infer_instance

def scalarCompletedTriaSquare :
    scalarCompletedTriaFunctor φ D S h h' ⋙
        (localCompletedQuotientEquivalence A' (DGBaseChange φ D) S h').functor ≅
      (localCompletedQuotientEquivalence A D S h).functor ⋙
        (functorExtension₂ _ _).obj (quotientScalarTriaFunctor φ S) :=
  karoubiFunctorSquare _ _ (localScalarTriaSquare φ S h h')

def scalarCompletedPerfectSquare :
    scalarCompletedTriaFunctor φ D S h h' ⋙
        (graphCompletedPerfectComparison A' (DGBaseChange φ D) S h').functor ≅
      (graphCompletedPerfectComparison A D S h).functor ⋙ quotientScalarPerfectFunctor φ D S :=
  (Functor.associator _ _ _).symm ≪≫
    isoWhiskerRight (scalarCompletedTriaSquare φ D S h h') _ ≪≫
    Functor.associator _ _ _ ≪≫
    isoWhiskerLeft _ (quotientScalarKaroubiPerfectSquare φ S) ≪≫
    (Functor.associator _ _ _).symm

/-- 完備化した tria 係数変更と、指定局所 perfect 同値の実際の正方形。 -/
def scalarCompletedLocalPerfectSquare :
    (localPerfectQuotientEquivalence A D S h).functor ⋙ scalarCompletedTriaFunctor φ D S h h' ≅
      quotientScalarPerfectHomotopyFunctor φ D S ⋙
        (localPerfectQuotientEquivalence A' (DGBaseChange φ D) S h').functor :=
  Functor.associator
      (perfectDGModuleHomotopyEquivalence A (QuotientObject D S) Set.univ).functor
      (graphCompletedPerfectComparison A D S h).inverse (scalarCompletedTriaFunctor φ D S h h') ≪≫
    isoWhiskerLeft _ (equivalenceInverseSquare
      (graphCompletedPerfectComparison A D S h)
      (graphCompletedPerfectComparison A' (DGBaseChange φ D) S h') _ _
      (scalarCompletedPerfectSquare φ D S h h')) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    isoWhiskerRight (quotientScalarPerfectHomotopySquare φ D S).symm _ ≪≫
    Functor.associator _ _ _

/-- tria を先に完備化する経路と、既存 perfect 比較で運ぶ経路は同じ係数変更を与える。 -/
def scalarCompletionComparisonIso :
    scalarCompletedTriaFunctor φ D S h h' ≅ completedScalarExtension φ D S h h' :=
  ((localPerfectQuotientEquivalence A D S h).congrLeft
    (E := CompletedTriaQuotient A' (DGBaseChange φ D) S)).inverse.preimageIso
      (scalarCompletedLocalPerfectSquare φ D S h h' ≪≫
        (localPerfectScalarExtensionSquare φ D S h h').symm)

/-- 未完備の指定商からの標準包含に対する、実際の Karoubi 完備化の係数変更正方形。 -/
def scalarCompletionToKaroubiSquare :
    toKaroubi (TriaQuotient A D S) ⋙ completedScalarExtension φ D S h h' ≅
      localScalarTriaExtension φ S h h' ⋙ toKaroubi (TriaQuotient A' (DGBaseChange φ D) S) :=
  isoWhiskerLeft _ (scalarCompletionComparisonIso φ D S h h').symm ≪≫
    (functorExtension₂CompWhiskeringLeftToKaroubiIso _ _).app
      (localScalarTriaExtension φ S h h')
end SerrePositivity.DifferentialGraded.DGQuotient
