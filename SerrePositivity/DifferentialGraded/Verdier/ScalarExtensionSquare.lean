module
public import SerrePositivity.DifferentialGraded.Verdier.ComparisonLinear
public import SerrePositivity.DifferentialGraded.Quotient.ScalarExtension
public import SerrePositivity.DifferentialGraded.Endomorphism.ScalarPerfectShiftTriangles
public import SerrePositivity.DifferentialGraded.Morita.PerfectQuasiEquivalenceTriangles

/-! # 非平坦係数変更と局所 perfect・完備 Verdier 商比較

U12f の実際の導来係数拡大と U15d の固定 path 比較を使う。
完備商上の関手は既存の局所 perfect 同値に沿って運ぶ。
これを未完備 tria の Verdier 局所化から直接構成した関手と同一視しない。
-/
@[expose] public section
noncomputable section
set_option synthInstance.maxSize 1024
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory CategoryTheory.Functor ScalarExtension
variable {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')
  (D : Type v) [DGCategory A D] [Small.{u} D] (S : Set D)

/-- 商の係数変更を行い、固定 path 比較の dg 関手に沿って延長した実際の Perf 関手。 -/
def quotientScalarPerfectFunctor :
    PerfectModuleCategory A (QuotientObject D S) ⥤
      PerfectModuleCategory A' (QuotientObject (DGBaseChange φ D) S) :=
  perfectScalarDerivedExtension φ (QuotientObject D S) Set.univ ⋙
    quasiEquivalencePerfectExtension A' (DGBaseChange φ (QuotientObject D S))
      (QuotientObject (DGBaseChange φ D) S) (quotientBaseChangeDGFunctor φ D S)

instance quotientScalarPerfectFunctorCommShift :
    (quotientScalarPerfectFunctor φ D S).CommShift ℤ := by
  letI := perfectScalarDerivedExtensionCommShift φ (QuotientObject D S) Set.univ
  letI := quasiEquivalencePerfectExtensionCommShift A'
    (DGBaseChange φ (QuotientObject D S)) (QuotientObject (DGBaseChange φ D) S)
    (quotientBaseChangeDGFunctor φ D S)
  dsimp [quotientScalarPerfectFunctor]
  infer_instance

instance quotientScalarPerfectFunctorIsTriangulated :
    (quotientScalarPerfectFunctor φ D S).IsTriangulated := by
  let := perfectScalarDerivedExtensionCommShift φ (QuotientObject D S) Set.univ
  let := quasiEquivalencePerfectExtensionCommShift A'
    (DGBaseChange φ (QuotientObject D S)) (QuotientObject (DGBaseChange φ D) S)
    (quotientBaseChangeDGFunctor φ D S)
  let := perfectScalarDerivedExtensionIsTriangulated φ (QuotientObject D S) Set.univ
  let := quasiEquivalencePerfectExtensionIsTriangulated A'
    (DGBaseChange φ (QuotientObject D S)) (QuotientObject (DGBaseChange φ D) S)
    (quotientBaseChangeDGFunctor φ D S)
  dsimp [quotientScalarPerfectFunctor]
  infer_instance

/-- Perf への制限を忘れると、U12f と U15d の実際の導来関手の合成に戻る。 -/
def quotientScalarPerfectInclusionIso :
    quotientScalarPerfectFunctor φ D S ⋙
        perfectModuleInclusion A' (QuotientObject (DGBaseChange φ D) S) Set.univ ≅
      perfectModuleInclusion A (QuotientObject D S) Set.univ ⋙
        derivedExtension φ (QuotientObject D S) ⋙
          dgDerivedExtension A' (DGBaseChange φ (QuotientObject D S))
            (QuotientObject (DGBaseChange φ D) S) (quotientBaseChangeDGFunctor φ D S) :=
  Iso.refl _

/-- 同じ係数変更を、既存の perfect enhancement の H⁰ に運んだ関手。 -/
def quotientScalarPerfectHomotopyFunctor :
    PerfectDGHomotopyCategoryOver A (QuotientObject D S) Set.univ ⥤
      PerfectDGHomotopyCategoryOver A' (QuotientObject (DGBaseChange φ D) S) Set.univ :=
  (perfectDGModuleHomotopyEquivalence A (QuotientObject D S) Set.univ).functor ⋙
    quotientScalarPerfectFunctor φ D S ⋙
      (perfectDGModuleHomotopyEquivalence A'
        (QuotientObject (DGBaseChange φ D) S) Set.univ).inverse

instance quotientScalarPerfectHomotopyFunctorCommShift :
    (quotientScalarPerfectHomotopyFunctor φ D S).CommShift ℤ := by
  dsimp [quotientScalarPerfectHomotopyFunctor]
  infer_instance

instance quotientScalarPerfectHomotopyFunctorIsTriangulated :
    (quotientScalarPerfectHomotopyFunctor φ D S).IsTriangulated := by
  dsimp [quotientScalarPerfectHomotopyFunctor]
  infer_instance

def quotientScalarPerfectHomotopySquare :
    quotientScalarPerfectHomotopyFunctor φ D S ⋙
        (perfectDGModuleHomotopyEquivalence A'
          (QuotientObject (DGBaseChange φ D) S) Set.univ).functor ≅
      (perfectDGModuleHomotopyEquivalence A (QuotientObject D S) Set.univ).functor ⋙
        quotientScalarPerfectFunctor φ D S :=
  Functor.associator _ _ _ ≪≫
    isoWhiskerLeft _ (Functor.associator _ _ _ ≪≫
      isoWhiskerLeft _ (perfectDGModuleHomotopyEquivalence A'
        (QuotientObject (DGBaseChange φ D) S) Set.univ).counitIso ≪≫
          Functor.rightUnitor _)

instance quotientScalarPerfectHomotopySquareCommShift :
    NatTrans.CommShift (quotientScalarPerfectHomotopySquare φ D S).hom ℤ := by
  dsimp only [quotientScalarPerfectHomotopySquare, Iso.trans_hom,
    isoWhiskerLeft_hom]
  infer_instance

def quotientScalarPerfectHomotopySquareTriangle :=
  Functor.mapTriangleIso (quotientScalarPerfectHomotopySquare φ D S)

variable (h : localKFlat A D S) (h' : localKFlat A' (DGBaseChange φ D) S)

/-- 完備 Verdier 商上の導来係数変更。両係数環での局所 K-flat 条件は別に受け取る。 -/
def completedScalarExtension :
    CompletedTriaQuotient A D S ⥤ CompletedTriaQuotient A' (DGBaseChange φ D) S :=
  (localPerfectQuotientEquivalence A D S h).inverse ⋙
    quotientScalarPerfectHomotopyFunctor φ D S ⋙
      (localPerfectQuotientEquivalence A' (DGBaseChange φ D) S h').functor

instance completedScalarExtensionCommShift :
    (completedScalarExtension φ D S h h').CommShift ℤ := by
  dsimp [completedScalarExtension]
  infer_instance

instance completedScalarExtensionIsTriangulated :
    (completedScalarExtension φ D S h h').IsTriangulated := by
  dsimp [completedScalarExtension]
  infer_instance

/-- 局所 perfect 比較と完備商上の係数変更の可換正方形。 -/
def localPerfectScalarExtensionSquare :
    (localPerfectQuotientEquivalence A D S h).functor ⋙
        completedScalarExtension φ D S h h' ≅
      quotientScalarPerfectHomotopyFunctor φ D S ⋙
        (localPerfectQuotientEquivalence A' (DGBaseChange φ D) S h').functor :=
  (Functor.associator _ _ _).symm ≪≫
    isoWhiskerRight (localPerfectQuotientEquivalence A D S h).unitIso.symm _ ≪≫
      Functor.leftUnitor _

instance localPerfectScalarExtensionSquareCommShift :
    NatTrans.CommShift (localPerfectScalarExtensionSquare φ D S h h').hom ℤ := by
  dsimp only [localPerfectScalarExtensionSquare, Iso.trans_hom, isoWhiskerRight_hom]
  infer_instance

def localPerfectScalarExtensionSquareTriangle :=
  Functor.mapTriangleIso (localPerfectScalarExtensionSquare φ D S h h')
end SerrePositivity.DifferentialGraded.DGQuotient
