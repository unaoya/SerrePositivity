module

public import SerrePositivity.DifferentialGraded.Quotient.DerivedComparison.Equivalence
public import SerrePositivity.DifferentialGraded.Derived.HomotopyLinear
public import SerrePositivity.CategoryTheory.ScalarSupport
public import Mathlib.CategoryTheory.Shift.Linear

/-!
# Verdier.Comparison

## 概要
2 本に分かれていた同主題の構成と比較をまとめる。

## 方針
対応表の依存順に連結し、元の宣言・証明・名前空間を保持する。

## 規約
各元ファイルの section を分離し、variable・option の局所的な作用を保つ。

## 使われ方
DifferentialGraded の入口と、この主題を使う検査・下流モジュールから import する。
-/

/-! ## ComparisonLinear（旧 SerrePositivity/DifferentialGraded/Verdier/ComparisonLinear.lean） -/

/-! # 局所 dg 商・perfect 比較の係数環上の線形性

既存の比較関手の定義と自然同型を使い、U17c の正方形の全辺に線形性を与える。
-/

@[expose] public section ComparisonLinear
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Functor Idempotents
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

instance derivedFiniteCellInclusionLinear (S : Set D) :
    (derivedFiniteCellInclusion A D S).Linear A where
  map_smul _ _ := rfl

instance homotopyFiniteCellToDerivedLinear (S : Set D) :
    (homotopyFiniteCellToDerived A D S).Linear A := by
  dsimp [homotopyFiniteCellToDerived]
  infer_instance
instance homotopyFiniteCellToTriaLinear (S : Set D) :
    (homotopyFiniteCellToTria A D S).Linear A where
  map_smul f r := by
    apply (derivedFiniteCellInclusion A D S).map_injective
    exact (homotopyFiniteCellToDerived A D S).map_smul r f
instance homotopyFiniteCellTriaEquivalenceFunctorLinear (S : Set D) :
    (homotopyFiniteCellTriaEquivalence A D S).functor.Linear A :=
  homotopyFiniteCellToTriaLinear A D S

instance moduleDerivedKaroubiEquivalenceFunctorLinear :
    (moduleDerivedKaroubiEquivalence A D).functor.Linear A := by
  change (toKaroubi (DerivedModuleCategory A D)).Linear A
  infer_instance
instance finiteCellKaroubiFunctorLinear (S : Set D) :
    (finiteCellKaroubiFunctor A D S).Linear A := by
  dsimp [finiteCellKaroubiFunctor]
  infer_instance
instance finiteCellKaroubiRealizationLinear (S : Set D) :
    (finiteCellKaroubiRealization A D S).Linear A := by
  dsimp [finiteCellKaroubiRealization]
  infer_instance
instance finiteCellKaroubiToPerfectLinear (S : Set D) :
    (finiteCellKaroubiToPerfect A D S).Linear A where
  map_smul f r := by
    apply (modulePerfectOver A D S).ι.map_injective
    exact (finiteCellKaroubiRealization A D S).map_smul r f
instance finiteCellKaroubiPerfectEquivalenceFunctorLinear (S : Set D) :
    (finiteCellKaroubiPerfectEquivalence A D S).functor.Linear A :=
  finiteCellKaroubiToPerfectLinear A D S

namespace DGQuotient
instance quotientCellToDerivedLinear (S : Set D) :
    (quotientCellToDerived A D S).Linear A := by
  dsimp [quotientCellToDerived]
  infer_instance
instance quotientTriaToDerivedLinear (S : Set D) :
    (quotientTriaToDerived A D S).Linear A := by
  dsimp [quotientTriaToDerived]
  infer_instance
instance quotientTriaFunctorLinear (S : Set D) :
    (quotientTriaFunctor A D S).Linear A where
  map_smul f r := by
    apply (triaInclusion A (QuotientObject D S)).map_injective
    exact (quotientTriaToDerived A D S).map_smul r f
instance quotientVerdierComparisonLinear (S : Set D) :
    (quotientVerdierComparison A D S).Linear A :=
  (Localization.functor_linear_iff (triaQuotient A D S) (triaImage A D S).trW A
    (quotientTriaFunctor A D S) (quotientVerdierComparison A D S)).mp inferInstance
instance localQuotientTriaFunctorLinear (S : Set D) :
    (localQuotientTriaFunctor A D S).Linear A :=
  Functor.linear_of_iso A (quotientComparisonModelsIso A D S).symm
instance localQuotientTriaEquivalenceFunctorLinear (S : Set D) (h : localKFlat A D S) :
    (localQuotientTriaEquivalence A D S h).functor.Linear A := by
  change (localQuotientTriaFunctor A D S).Linear A
  infer_instance
instance localCompletedQuotientEquivalenceFunctorLinear (S : Set D) (h : localKFlat A D S) :
    (localCompletedQuotientEquivalence A D S h).functor.Linear A := by
  change ((functorExtension₂ _ _).obj (localQuotientTriaEquivalence A D S h).functor).Linear A
  infer_instance
instance localPerfectQuotientEquivalenceFunctorLinear (S : Set D) (h : localKFlat A D S) :
    (localPerfectQuotientEquivalence A D S h).functor.Linear A := by
  dsimp [localPerfectQuotientEquivalence]
  infer_instance
instance localSmallPerfectQuotientEquivalenceFunctorLinear (S : Set D) (h : localKFlat A D S) :
    (localSmallPerfectQuotientEquivalence A D S h).functor.Linear A := by
  dsimp [localSmallPerfectQuotientEquivalence]
  infer_instance
instance localPerfectKaroubiFirstEquivalenceFunctorLinear (S : Set D) (h : localKFlat A D S) :
    (localPerfectKaroubiFirstEquivalence A D S h).functor.Linear A := by
  dsimp [localPerfectKaroubiFirstEquivalence]
  infer_instance
end DGQuotient
end SerrePositivity.DifferentialGraded
end

end ComparisonLinear

/-! ## SupportSquare（旧 SerrePositivity/DifferentialGraded/Verdier/SupportSquare.lean） -/

/-! # 局所商比較の支持部分圏への制限と忘却正方形 -/

@[expose] public section SupportSquare
universe u v

noncomputable section
set_option synthInstance.maxSize 1024
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
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
end

end SupportSquare
