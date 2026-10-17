module
public import SerrePositivity.DifferentialGraded.Verdier.MoritaPairEquivalence
public import SerrePositivity.DifferentialGraded.Morita.QuasiEquivalenceDerivedGraph

/-! # U16b の dg 擬同値から得る、指定局所 perfect 商上の Morita 同値

元の Perf 作用の同値性は U16b から証明する。
指定零部分圏の対応と局所 K-flat 条件は、それとは独立に明示する。
-/
@[expose] public section
noncomputable section
set_option synthInstance.maxSize 1024
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded
open CategoryTheory CategoryTheory.Functor Morita
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E] (F : DGFunctor A D E)

lemma graphPairKernelColumnsPerfect : kernelColumnsPerfect A D E (kernelGraph A D E F) :=
  (kernelColumnsPerfect_iff_preservesPerfect A D E _).2
    (fun _ hX => quasiEquivalenceDerivedGraph_perfect A D E F hX)

/-- U16b の実際の graph 同型を用いた、元の主 Perf 作用の Morita 性。 -/
lemma graphPairKernelPerfectIsEquivalence (hF : QuasiEquivalence F) :
    (perfectDerivedKernelAction A D E (kernelGraph A D E F)
      (graphPairKernelColumnsPerfect A D E F)).IsEquivalence := by
  let : (quasiEquivalencePerfectExtension A D E F).IsEquivalence :=
    (quasiEquivalencePerfectEquivalence A D E F hF).isEquivalence_functor
  exact Functor.isEquivalence_of_iso (quasiEquivalenceDerivedGraphOnPerfectIso A D E F).symm

variable (S : Set D) (T : Set E) (hST : ∀ d ∈ S, F.obj d ∈ T)

include hST in
lemma graphPairKernelSupportedColumns (d : D) (hd : d ∈ S) :
    modulePerfectOver A E T ((kernelDerivedColumn A D E d).obj (kernelGraph A D E F)) := by
  let e := (kernelDerivedColumnActionIso A D E (kernelGraph A D E F) d).symm ≪≫
    (quasiEquivalenceDerivedGraphIso A D E F).app
      ((moduleToDerived A D).obj (ForgetEnrichment.of (Complex A) (representable A d))) ≪≫
    dgDerivedExtensionRepresentableIso A D E F d
  exact (modulePerfectOver A E T).prop_of_iso e.symm
    ((derivedFiniteCellOver A E T).le_retractClosure _
      ((moduleFiniteCellOver A E T).prop_map_obj (moduleToDerived A E)
        (moduleFiniteCellOver_representable A E (F.obj d) (hST d hd))))

namespace DGQuotient
variable (hF : QuasiEquivalence F)
  (hReflect : ∀ X : PerfectModuleCategory A D,
    perfectNullObjects A E T
        ((perfectDerivedKernelAction A D E (kernelGraph A D E F)
          (graphPairKernelColumnsPerfect A D E F)).obj X) → perfectNullObjects A D S X)
  (hD : localKFlat A D S) (hE : localKFlat A E T)

/-- 商の同値性を仮定せず、U16b と指定零部分圏の反映から得る局所 Morita 同値。 -/
def graphPairLocalMoritaEquivalence :
    PerfectDGHomotopyCategoryOver A (QuotientObject D S) Set.univ ≌
      PerfectDGHomotopyCategoryOver A (QuotientObject E T) Set.univ :=
  mainKernelLocalMoritaEquivalence A D E (kernelGraph A D E F)
    (graphPairKernelColumnsPerfect A D E F) S T
    (graphPairKernelSupportedColumns A D E F S T hST) hReflect
    (graphPairKernelPerfectIsEquivalence A D E F hF) hD hE

instance graphPairLocalMoritaFunctorCommShift :
    (graphPairLocalMoritaEquivalence A D E F S T hST hF hReflect hD hE).functor.CommShift ℤ :=
  mainKernelLocalMoritaFunctorCommShift _ _ _ _ _ _ _ _ _ _ _ _
instance graphPairLocalMoritaInverseCommShift :
    (graphPairLocalMoritaEquivalence A D E F S T hST hF hReflect hD hE).inverse.CommShift ℤ :=
  mainKernelLocalMoritaInverseCommShift _ _ _ _ _ _ _ _ _ _ _ _
instance graphPairLocalMoritaCommShift :
    (graphPairLocalMoritaEquivalence A D E F S T hST hF hReflect hD hE).CommShift ℤ :=
  mainKernelLocalMoritaCommShift _ _ _ _ _ _ _ _ _ _ _ _

instance graphPairLocalMoritaIsTriangulated :
    (graphPairLocalMoritaEquivalence A D E F S T hST hF hReflect hD hE).IsTriangulated :=
  mainKernelLocalMoritaIsTriangulated _ _ _ _ _ _ _ _ _ _ _ _

/-- U16b による Morita 同値も、元の作用から誘導した完備商関手と局所比較を可換にする。 -/
def graphPairLocalMoritaSquare :=
  mainKernelMoritaLocalPerfectSquare A D E (kernelGraph A D E F)
    (graphPairKernelColumnsPerfect A D E F) S T
    (graphPairKernelSupportedColumns A D E F S T hST) hReflect
    (graphPairKernelPerfectIsEquivalence A D E F hF) hD hE

instance graphPairLocalMoritaSquareCommShift :
    NatTrans.CommShift (graphPairLocalMoritaSquare A D E F S T hST hF hReflect hD hE).hom ℤ :=
  mainKernelMoritaLocalPerfectSquareCommShift _ _ _ _ _ _ _ _ _ _ _ _

def graphPairLocalMoritaSquareTriangle :=
  Functor.mapTriangleIso (graphPairLocalMoritaSquare A D E F S T hST hF hReflect hD hE)
end DGQuotient
end SerrePositivity.DifferentialGraded
