module
public import SerrePositivity.DifferentialGraded.Verdier.KernelLocalPerfectSquare

/-! # 指定零部分圏を対応させる Morita 作用の商上の同値

実際の主 Perf 作用の同値性と、零部分圏の反映をそれぞれ明示する。
商上の同値や比較正方形の存在を入力にはしない。
-/
@[expose] public section
noncomputable section
set_option synthInstance.maxSize 1024
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded
open CategoryTheory CategoryTheory.Functor Idempotents Morita
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E] (K : Kernel A D E)
  (hK : kernelColumnsPerfect A D E K) (S : Set D) (T : Set E)
  (hST : ∀ d ∈ S, modulePerfectOver A E T ((kernelDerivedColumn A D E d).obj K))
  (hReflect : ∀ X : PerfectModuleCategory A D,
    perfectNullObjects A E T ((perfectDerivedKernelAction A D E K hK).obj X) →
      perfectNullObjects A D S X)

local instance moritaPairKernelShift : (perfectDerivedKernelAction A D E K hK).CommShift ℤ :=
  mainPerfectKernelActionCommShift A D E K hK
local instance moritaPairKernelTriangles :
    (perfectDerivedKernelAction A D E K hK).IsTriangulated :=
  mainPerfectKernelActionIsTriangulated A D E K hK

include hST hReflect in
lemma perfectKernelPairDenominators :
    (perfectNullObjects A D S).trW = (perfectNullObjects A E T).trW.inverseImage
      (perfectDerivedKernelAction A D E K hK) := by
  have hp : perfectNullObjects A D S = (perfectNullObjects A E T).inverseImage
      (perfectDerivedKernelAction A D E K hK) := by
    ext X
    exact ⟨perfectKernelNullObjects_image A D E K hK S T hST X, hReflect X⟩
  rw [hp]
  ext X Y f
  exact (perfectNullObjects A E T).inverseImage_trW_iff _ f

variable (hMorita : (perfectDerivedKernelAction A D E K hK).IsEquivalence)

include hReflect hMorita in
lemma perfectKernelPairVerdierIsEquivalence :
    (perfectKernelVerdierFunctor A D E K hK S T hST).IsEquivalence := by
  let Φ := LocalizerMorphism.ofEq (perfectKernelPairDenominators A D E K hK S T hST hReflect)
  have : Φ.functor.IsEquivalence := hMorita
  have : Φ.IsLocalizedEquivalence :=
    LocalizerMorphism.IsLocalizedEquivalence.of_equivalence Φ (by
      change (perfectNullObjects A E T).trW ≤
        (perfectNullObjects A D S).trW.map (perfectDerivedKernelAction A D E K hK)
      rw [perfectKernelPairDenominators A D E K hK S T hST hReflect,
        MorphismProperty.map_inverseImage_eq_of_isEquivalence])
  have : CatCommSq Φ.functor (perfectVerdierQuotient A D S) (perfectVerdierQuotient A E T)
      (perfectKernelVerdierFunctor A D E K hK S T hST) :=
    CatCommSq.mk (perfectKernelVerdierSquare A D E K hK S T hST).symm
  exact LocalizerMorphism.isEquivalence Φ
    (perfectVerdierQuotient A D S) (perfectVerdierQuotient A E T)
    (perfectKernelVerdierFunctor A D E K hK S T hST)

def perfectKernelPairVerdierEquivalence :
    PerfectVerdierQuotient A D S ≌ PerfectVerdierQuotient A E T :=
  letI := perfectKernelPairVerdierIsEquivalence A D E K hK S T hST hReflect hMorita
  (perfectKernelVerdierFunctor A D E K hK S T hST).asEquivalence

include hReflect hMorita in
lemma perfectKernelPairCompletedIsEquivalence :
    (perfectKernelCompletedVerdierFunctor A D E K hK S T hST).IsEquivalence :=
  (karoubiEquivalenceTransport
    (perfectKernelPairVerdierEquivalence A D E K hK S T hST hReflect hMorita)).isEquivalence_functor

namespace DGQuotient
variable (hD : localKFlat A D S) (hE : localKFlat A E T)

/-- 元の kernel の Morita 性と零部分圏の対応から、指定完備商上でも同値を得る。 -/
def mainKernelCompletedMoritaEquivalence :
    CompletedTriaQuotient A D S ≌ CompletedTriaQuotient A E T := by
  let := perfectKernelPairCompletedIsEquivalence A D E K hK S T hST hReflect hMorita
  have : (mainKernelCompletedQuotientFunctor A D S E K hK T hST).IsEquivalence := by
    dsimp [mainKernelCompletedQuotientFunctor]
    infer_instance
  exact (mainKernelCompletedQuotientFunctor A D S E K hK T hST).asEquivalence

/-- 実際に局所化した kernel 作用の、商 perfect enhancement の H⁰ 上の Morita 同値。 -/
def mainKernelLocalMoritaEquivalence :
    PerfectDGHomotopyCategoryOver A (QuotientObject D S) Set.univ ≌
      PerfectDGHomotopyCategoryOver A (QuotientObject E T) Set.univ := by
  let := perfectKernelPairCompletedIsEquivalence A D E K hK S T hST hReflect hMorita
  have : (mainKernelQuotientPerfectHomotopyFunctor A D S hD E K hK T hST hE).IsEquivalence := by
    dsimp [mainKernelQuotientPerfectHomotopyFunctor]
    infer_instance
  exact (mainKernelQuotientPerfectHomotopyFunctor A D S hD E K hK T hST hE).asEquivalence

instance mainKernelLocalMoritaFunctorCommShift :
    (mainKernelLocalMoritaEquivalence
      A D E K hK S T hST hReflect hMorita hD hE).functor.CommShift ℤ :=
  mainKernelQuotientPerfectHomotopyFunctorCommShift A D S hD E K hK T hST hE
instance mainKernelLocalMoritaInverseCommShift :
    (mainKernelLocalMoritaEquivalence
      A D E K hK S T hST hReflect hMorita hD hE).inverse.CommShift ℤ :=
  (mainKernelLocalMoritaEquivalence A D E K hK S T hST hReflect hMorita hD hE).commShiftInverse ℤ
instance mainKernelLocalMoritaCommShift :
    (mainKernelLocalMoritaEquivalence A D E K hK S T hST hReflect hMorita hD hE).CommShift ℤ :=
  (mainKernelLocalMoritaEquivalence
    A D E K hK S T hST hReflect hMorita hD hE).commShift_of_functor ℤ
instance mainKernelLocalMoritaIsTriangulated :
    (mainKernelLocalMoritaEquivalence A D E K hK S T hST hReflect hMorita hD hE).IsTriangulated :=
  Equivalence.IsTriangulated.mk' _
    (mainKernelQuotientPerfectHomotopyFunctorIsTriangulated A D S hD E K hK T hST hE)

/-- Morita 同値の場合にも、既存の局所 perfect 比較と実際の誘導完備商関手が可換する。 -/
def mainKernelMoritaLocalPerfectSquare :
    (localPerfectQuotientEquivalence A D S hD).functor ⋙
        mainKernelCompletedQuotientFunctor A D S E K hK T hST ≅
      (mainKernelLocalMoritaEquivalence A D E K hK S T hST hReflect hMorita hD hE).functor ⋙
        (localPerfectQuotientEquivalence A E T hE).functor :=
  mainKernelLocalPerfectSquare A D S hD E K hK T hST hE

instance mainKernelMoritaLocalPerfectSquareCommShift :
    NatTrans.CommShift
      (mainKernelMoritaLocalPerfectSquare A D E K hK S T hST hReflect hMorita hD hE).hom ℤ :=
  mainKernelLocalPerfectSquareCommShift A D S hD E K hK T hST hE

def mainKernelMoritaLocalPerfectSquareTriangle :=
  Functor.mapTriangleIso
    (mainKernelMoritaLocalPerfectSquare A D E K hK S T hST hReflect hMorita hD hE)
end DGQuotient
end SerrePositivity.DifferentialGraded
