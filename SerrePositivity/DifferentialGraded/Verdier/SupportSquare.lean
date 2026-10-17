module
public import SerrePositivity.DifferentialGraded.Verdier.ComparisonLinear
public import SerrePositivity.CategoryTheory.ScalarSupportEquivalence
public import Mathlib.CategoryTheory.Shift.Linear

/-! # 局所商比較の支持部分圏への制限と忘却正方形 -/
@[expose] public section
noncomputable section
set_option synthInstance.maxSize 1024
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits

section General
variable {R : Type*} [CommRing R] {C T : Type*} [Category* C] [Category* T]
  [Preadditive C] [Preadditive T] [Linear R C] [Linear R T]
  (E : C ≌ T) [E.functor.Linear R] [E.functor.Additive] {e : ℕ} (z : Fin e → R)

/-- 支持部分圏の比較は、元の比較と忘却関手の正方形を作る。 -/
def supportForgetSquare :
    (scalarSupportEquivalence E z).functor ⋙ (scalarSupported (C := T) z).ι ≅
      (scalarSupported (C := C) z).ι ⋙ E.functor :=
  (scalarSupported (C := T) z).liftCompιIso _ _

instance supportEquivalenceFunctorLinear : (scalarSupportEquivalence E z).functor.Linear R where
  map_smul f r := by
    apply (scalarSupported (C := T) z).ι.map_injective
    exact E.functor.map_smul r f.hom

variable [HasZeroObject C] [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [∀ n : ℤ, (shiftFunctor C n).Linear R] [Pretriangulated C]
  [HasZeroObject T] [HasShift T ℤ] [∀ n : ℤ, (shiftFunctor T n).Additive]
  [∀ n : ℤ, (shiftFunctor T n).Linear R] [Pretriangulated T]
  [E.functor.CommShift ℤ] [E.functor.IsTriangulated]

instance supportForgetSquareCommShift : NatTrans.CommShift (supportForgetSquare E z).hom ℤ := by
  dsimp [supportForgetSquare]
  infer_instance

/-- 支持部分圏の忘却正方形を三角形関手へ適用した自然同型。 -/
def supportForgetSquareTriangle := Functor.mapTriangleIso (supportForgetSquare E z)
end General

lemma supportShiftLinearOfFaithful {R : Type*} [CommRing R]
    {C T : Type*} [Category* C] [Category* T] [Preadditive C] [Preadditive T]
    [Linear R C] [Linear R T] [HasShift C ℤ] [HasShift T ℤ]
    (F : C ⥤ T) [F.Faithful] [F.Linear R] [F.CommShift ℤ]
    [∀ n : ℤ, (shiftFunctor T n).Linear R] (n : ℤ) :
    (shiftFunctor C n).Linear R where
  map_smul f r := by
    apply F.map_injective
    have : (shiftFunctor C n ⋙ F).Linear R :=
      Functor.linear_of_iso R (F.commShiftIso n).symm
    exact ((shiftFunctor C n ⋙ F).map_smul r f).trans
      (F.map_smul r ((shiftFunctor C n).map f)).symm

section ShiftLinear
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

instance supportModuleEvaluationLinear (x : D) : (moduleEvaluation A D x).Linear A := by
  dsimp [moduleEvaluation]
  infer_instance

instance supportModuleShiftLinear (n : ℤ) :
    (shiftFunctor (ModuleCategory A D) n).Linear A where
  map_smul f r := by
    apply moduleMorphism_ext
    intro x
    change (moduleEvaluation A D x).map (moduleShiftMap A D n (r • f)) =
      (moduleEvaluation A D x).map (r • moduleShiftMap A D n f)
    simp only [moduleShiftMap_eval, CategoryTheory.Functor.map_smul]

instance supportDerivedShiftLinear (n : ℤ) :
    (shiftFunctor (DerivedModuleCategory A D) n).Linear A :=
  Shift.linear_of_localization A (moduleToDerived A D) (moduleQuasiIso A D) n

instance supportTriaShiftLinear (n : ℤ) :
    (shiftFunctor (TriaCategory A D) n).Linear A :=
  supportShiftLinearOfFaithful (triaInclusion A D) n

instance supportPerfectShiftLinear (S : Set D) (n : ℤ) :
    (shiftFunctor (PerfectDGHomotopyCategoryOver A D S) n).Linear A :=
  supportShiftLinearOfFaithful
    (perfectDGModuleToPerfect A D S ⋙ (modulePerfectOver A D S).ι) n
end ShiftLinear

namespace DGQuotient
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (S : Set D) (h : localKFlat A D S) {e : ℕ} (z : Fin e → A)

/-- 局所 K-flat 商比較は、同じスカラーで支持される tria の同値を誘導する。 -/
def localSupportedTriaEquivalence :=
  scalarSupportEquivalence (localQuotientTriaEquivalence A D S h) z

lemma localTriaSupport_iff (X : TriaQuotient A D S) :
    scalarSupported z ((localQuotientTriaEquivalence A D S h).functor.obj X) ↔
      scalarSupported z X :=
  scalarSupported_equivalence_iff (localQuotientTriaEquivalence A D S h) z X

def localTriaSupportSquare := supportForgetSquare (localQuotientTriaEquivalence A D S h) z

instance localSupportedTriaFunctorCommShift :
    (localSupportedTriaEquivalence A D S h z).functor.CommShift ℤ := by
  dsimp [localSupportedTriaEquivalence]
  infer_instance

instance localSupportedTriaInverseCommShift :
    (localSupportedTriaEquivalence A D S h z).inverse.CommShift ℤ :=
  (localSupportedTriaEquivalence A D S h z).commShiftInverse ℤ

instance localSupportedTriaEquivalenceCommShift :
    (localSupportedTriaEquivalence A D S h z).CommShift ℤ := by
  dsimp [localSupportedTriaEquivalence]
  infer_instance

instance localSupportedTriaEquivalenceIsTriangulated :
    (localSupportedTriaEquivalence A D S h z).IsTriangulated := by
  dsimp [localSupportedTriaEquivalence]
  infer_instance

instance localTriaSupportSquareCommShift :
    NatTrans.CommShift (localTriaSupportSquare A D S h z).hom ℤ := by
  dsimp [localTriaSupportSquare]
  infer_instance

/-- Karoubi 完備化した局所商比較についても支持を保存・反映する。 -/
def localSupportedCompletedEquivalence :=
  scalarSupportEquivalence (localCompletedQuotientEquivalence A D S h) z

def localCompletedSupportSquare :=
  supportForgetSquare (localCompletedQuotientEquivalence A D S h) z

instance localSupportedCompletedFunctorCommShift :
    (localSupportedCompletedEquivalence A D S h z).functor.CommShift ℤ := by
  dsimp [localSupportedCompletedEquivalence]
  infer_instance

instance localSupportedCompletedInverseCommShift :
    (localSupportedCompletedEquivalence A D S h z).inverse.CommShift ℤ :=
  (localSupportedCompletedEquivalence A D S h z).commShiftInverse ℤ

instance localSupportedCompletedEquivalenceCommShift :
    (localSupportedCompletedEquivalence A D S h z).CommShift ℤ :=
  (localSupportedCompletedEquivalence A D S h z).commShift_of_functor ℤ

instance localSupportedCompletedEquivalenceIsTriangulated :
    (localSupportedCompletedEquivalence A D S h z).IsTriangulated := by
  dsimp [localSupportedCompletedEquivalence]
  infer_instance

instance localCompletedSupportSquareCommShift :
    NatTrans.CommShift (localCompletedSupportSquare A D S h z).hom ℤ := by
  dsimp [localCompletedSupportSquare]
  infer_instance

/-- 実際の perfect enhancement 比較を、支持部分圏へ制限した同値。 -/
def localSupportedPerfectEquivalence :=
  scalarSupportEquivalence (localPerfectQuotientEquivalence A D S h) z

def localPerfectSupportSquare :=
  supportForgetSquare (localPerfectQuotientEquivalence A D S h) z

instance localSupportedPerfectFunctorCommShift :
    (localSupportedPerfectEquivalence A D S h z).functor.CommShift ℤ := by
  dsimp [localSupportedPerfectEquivalence]
  infer_instance

instance localSupportedPerfectInverseCommShift :
    (localSupportedPerfectEquivalence A D S h z).inverse.CommShift ℤ :=
  (localSupportedPerfectEquivalence A D S h z).commShiftInverse ℤ

instance localSupportedPerfectEquivalenceCommShift :
    (localSupportedPerfectEquivalence A D S h z).CommShift ℤ :=
  (localSupportedPerfectEquivalence A D S h z).commShift_of_functor ℤ

instance localSupportedPerfectEquivalenceIsTriangulated :
    (localSupportedPerfectEquivalence A D S h z).IsTriangulated := by
  dsimp [localSupportedPerfectEquivalence]
  infer_instance

instance localPerfectSupportSquareCommShift :
    NatTrans.CommShift (localPerfectSupportSquare A D S h z).hom ℤ := by
  dsimp [localPerfectSupportSquare]
  infer_instance

def localPerfectSupportSquareTriangle :=
  supportForgetSquareTriangle (localPerfectQuotientEquivalence A D S h) z
end DGQuotient
end SerrePositivity.DifferentialGraded
