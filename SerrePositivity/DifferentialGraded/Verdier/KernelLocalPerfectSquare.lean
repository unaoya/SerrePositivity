module
public import SerrePositivity.DifferentialGraded.Verdier.PerfectQuotientEquivalence

/-! # 一般 kernel から誘導した商作用と既存局所 perfect enhancement 比較の正方形

主 Perf の実作用を先に局所化し、指定商の同値を通して H⁰ へ運ぶ。
この H⁰ の運搬だけから新しい dg 関手の存在を結論しない。
-/
@[expose] public section
noncomputable section
set_option synthInstance.maxSize 1024
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory CategoryTheory.Functor Idempotents Morita
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (S : Set D) (hD : localKFlat A D S)

/-- 指定 Perf 商へ表示し直した局所同値は、元の局所 perfect 比較へ戻る。 -/
def localPerfectVerdierFactors :
    (localPerfectToPerfectVerdierEquivalence A D S hD).functor ⋙
        (perfectCompletedToTriaQuotientEquivalence A D S).functor ≅
      (localPerfectQuotientEquivalence A D S hD).functor :=
  Functor.associator _ _ _ ≪≫
    isoWhiskerLeft _ (perfectCompletedToTriaQuotientEquivalence A D S).counitIso ≪≫
      Functor.rightUnitor _

instance localPerfectVerdierFactorsCommShift :
    NatTrans.CommShift (localPerfectVerdierFactors A D S hD).hom ℤ := by
  dsimp only [localPerfectVerdierFactors, Iso.trans_hom, isoWhiskerLeft_hom]
  infer_instance

variable (E : Type w) [DGCategory A E] [Small.{u} E] (K : Kernel A D E)
  (hK : kernelColumnsPerfect A D E K) (T : Set E)
  (hST : ∀ d ∈ S, modulePerfectOver A E T ((kernelDerivedColumn A D E d).obj K))
  (hE : localKFlat A E T)

instance perfectKernelCompletedVerdierFunctorCommShift :
    (perfectKernelCompletedVerdierFunctor A D E K hK S T hST).CommShift ℤ := by
  dsimp [perfectKernelCompletedVerdierFunctor]
  infer_instance
instance perfectKernelCompletedVerdierFunctorIsTriangulated :
    (perfectKernelCompletedVerdierFunctor A D E K hK S T hST).IsTriangulated := by
  dsimp [perfectKernelCompletedVerdierFunctor]
  infer_instance

/-- 一般 kernel の実際の Perf 作用の局所化を、指定完備 tria 商へ表示する。 -/
def mainKernelCompletedQuotientFunctor :
    CompletedTriaQuotient A D S ⥤ CompletedTriaQuotient A E T :=
  (perfectCompletedToTriaQuotientEquivalence A D S).inverse ⋙
    perfectKernelCompletedVerdierFunctor A D E K hK S T hST ⋙
      (perfectCompletedToTriaQuotientEquivalence A E T).functor

instance mainKernelCompletedQuotientFunctorCommShift :
    (mainKernelCompletedQuotientFunctor A D S E K hK T hST).CommShift ℤ := by
  dsimp [mainKernelCompletedQuotientFunctor]
  infer_instance
instance mainKernelCompletedQuotientFunctorIsTriangulated :
    (mainKernelCompletedQuotientFunctor A D S E K hK T hST).IsTriangulated := by
  dsimp [mainKernelCompletedQuotientFunctor]
  infer_instance

/-- 実際に局所化した kernel 作用を、商の perfect enhancement の H⁰ に運ぶ。 -/
def mainKernelQuotientPerfectHomotopyFunctor :
    PerfectDGHomotopyCategoryOver A (QuotientObject D S) Set.univ ⥤
      PerfectDGHomotopyCategoryOver A (QuotientObject E T) Set.univ :=
  (localPerfectToPerfectVerdierEquivalence A D S hD).functor ⋙
    perfectKernelCompletedVerdierFunctor A D E K hK S T hST ⋙
      (localPerfectToPerfectVerdierEquivalence A E T hE).inverse

instance mainKernelQuotientPerfectHomotopyFunctorCommShift :
    (mainKernelQuotientPerfectHomotopyFunctor A D S hD E K hK T hST hE).CommShift ℤ := by
  dsimp [mainKernelQuotientPerfectHomotopyFunctor]
  infer_instance
instance mainKernelQuotientPerfectHomotopyFunctorIsTriangulated :
    (mainKernelQuotientPerfectHomotopyFunctor A D S hD E K hK T hST hE).IsTriangulated := by
  dsimp [mainKernelQuotientPerfectHomotopyFunctor]
  infer_instance

def mainKernelPerfectVerdierSquare :
    mainKernelQuotientPerfectHomotopyFunctor A D S hD E K hK T hST hE ⋙
        (localPerfectToPerfectVerdierEquivalence A E T hE).functor ≅
      (localPerfectToPerfectVerdierEquivalence A D S hD).functor ⋙
        perfectKernelCompletedVerdierFunctor A D E K hK S T hST :=
  Functor.associator _ _ _ ≪≫ isoWhiskerLeft _ (Functor.associator _ _ _ ≪≫
    isoWhiskerLeft _ (localPerfectToPerfectVerdierEquivalence A E T hE).counitIso ≪≫
      Functor.rightUnitor _)

instance mainKernelPerfectVerdierSquareCommShift :
    NatTrans.CommShift (mainKernelPerfectVerdierSquare A D S hD E K hK T hST hE).hom ℤ := by
  dsimp only [mainKernelPerfectVerdierSquare, Iso.trans_hom, isoWhiskerLeft_hom]
  infer_instance

/-- 一般主導来 kernel と既存の局所 perfect enhancement 比較そのものの正方形。 -/
def mainKernelLocalPerfectSquare :
    (localPerfectQuotientEquivalence A D S hD).functor ⋙
        mainKernelCompletedQuotientFunctor A D S E K hK T hST ≅
      mainKernelQuotientPerfectHomotopyFunctor A D S hD E K hK T hST hE ⋙
        (localPerfectQuotientEquivalence A E T hE).functor :=
  (Functor.associator _ _ _).symm ≪≫ (Functor.associator _ _ _).symm ≪≫
    isoWhiskerRight (mainKernelPerfectVerdierSquare A D S hD E K hK T hST hE).symm _ ≪≫
    Functor.associator _ _ _ ≪≫ isoWhiskerLeft _ (localPerfectVerdierFactors A E T hE)

instance mainKernelLocalPerfectSquareCommShift :
    NatTrans.CommShift (mainKernelLocalPerfectSquare A D S hD E K hK T hST hE).hom ℤ := by
  dsimp only [mainKernelLocalPerfectSquare, Iso.trans_hom, isoWhiskerRight_hom, isoWhiskerLeft_hom]
  infer_instance

def mainKernelLocalPerfectSquareTriangle :=
  Functor.mapTriangleIso (mainKernelLocalPerfectSquare A D S hD E K hK T hST hE)
end SerrePositivity.DifferentialGraded.DGQuotient
