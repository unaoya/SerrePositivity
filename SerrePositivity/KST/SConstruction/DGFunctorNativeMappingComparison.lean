module
public import SerrePositivity.KST.SConstruction.DGCoherentComparisonNaturality
public import SerrePositivity.KST.SConstruction.DGFunctorMappingSpace
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Quasicategory

/-! # 元の dg 関手写像空間の DK/native 比較と横合成
概要：既存 DK core から native core へ比較し、元の前後合成と tensor 横合成を照合する。
方針：全次数 dg 関手圏へ元の DK 比較を適用し、厳密 dg 入力自然性を core に制限する。
規約：tensor source の core を直積と同一視しない。使われ方：豊穣入力の実横合成。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories

variable (A : Type u) [CommRing A] (D E B : Type v)
  [DGCategory A D] [DGCategory A E] [DGCategory A B] [Small.{u} D]

/-- 元の全次数 dg 関手圏の native dg nerve の core。 -/
def dgFunctorNativeMappingSpace : SSet.{max u v} :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A (DGFunctor A D E)) : SSet)

/-- 元の全次数 dg 関手圏の native core は Kan 複体。 -/
instance dgFunctorNativeMappingSpace_kan : KanComplex (dgFunctorNativeMappingSpace A D E) := by
  change KanComplex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A (DGFunctor A D E)) : SSet)
  infer_instance

/-- 元の DK core と同じ全次数 dg 関手圏の native core の実比較。 -/
def dgFunctorMappingNativeComparison :
    dgFunctorMappingSpace A D E ⟶ dgFunctorNativeMappingSpace A D E :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreMap (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentComparison (R := A) (D := DGFunctor A D E))

/-- 元の厳密 dg 後合成による native core の実単体的写像。 -/
def dgFunctorNativeMappingPost (H : DGFunctor A E B) :
    dgFunctorNativeMappingSpace A D E ⟶ dgFunctorNativeMappingSpace A D B :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreMap (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgFunctorPostDG A D E B H))

/-- 元の DK/native core 比較は、元の全次数 dg 後合成と可換。 -/
lemma dgFunctorMappingNativeComparison_post (H : DGFunctor A E B) :
    dgFunctorMappingPost A D E B H ≫ dgFunctorMappingNativeComparison A D B =
      dgFunctorMappingNativeComparison A D E ≫ dgFunctorNativeMappingPost A D E B H := by
  ext n x
  apply Subtype.ext
  exact congrArg (fun f => (f.app n) x.val)
    (dgCoherentComparison_naturality (dgFunctorPostDG A D E B H))

variable [Small.{u} B]

/-- 元の厳密 dg 前合成による native core の実単体的写像。 -/
def dgFunctorNativeMappingPre (H : DGFunctor A B D) :
    dgFunctorNativeMappingSpace A D E ⟶ dgFunctorNativeMappingSpace A B E :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreMap (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgFunctorPreDG A D E B H))

/-- 元の DK/native core 比較は、元の全次数 dg 前合成と可換。 -/
lemma dgFunctorMappingNativeComparison_pre (H : DGFunctor A B D) :
    dgFunctorMappingPre A D E B H ≫ dgFunctorMappingNativeComparison A B E =
      dgFunctorMappingNativeComparison A D E ≫ dgFunctorNativeMappingPre A D E B H := by
  ext n x
  apply Subtype.ext
  exact congrArg (fun f => (f.app n) x.val)
    (dgCoherentComparison_naturality (dgFunctorPreDG A D E B H))

variable [Small.{u} E]

/-- 元の tensor dg 関手圏の native dg nerve の core。 -/
def dgFunctorNativeTensorMappingSpace : SSet.{max u v} :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A
    (DGTensorCategory A (DGFunctor A D E) (DGFunctor A E B))) : SSet)

/-- 元の tensor dg 関手圏の native core は Kan 複体。 -/
instance dgFunctorNativeTensorMappingSpace_kan :
    KanComplex (dgFunctorNativeTensorMappingSpace A D E B) := by
  change KanComplex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A
    (DGTensorCategory A (DGFunctor A D E) (DGFunctor A E B))) : SSet)
  infer_instance

/-- 同じ元の tensor dg 関手圏の DK/native core 比較。 -/
def dgFunctorTensorMappingNativeComparison :
    dgFunctorTensorMappingSpace A D E B ⟶ dgFunctorNativeTensorMappingSpace A D E B :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreMap (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentComparison (R := A)
    (D := DGTensorCategory A (DGFunctor A D E) (DGFunctor A E B)))

/-- 元の tensor dg 横合成による native core の実単体的写像。 -/
def dgFunctorNativeMappingHorizontal :
    dgFunctorNativeTensorMappingSpace A D E B ⟶ dgFunctorNativeMappingSpace A D B :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreMap (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgFunctorHorizontalDG A D E B))

omit [Small.{u} B] in
/-- 既存の tensor source 上の全横合成は、DK/native core 比較と厳密に可換。 -/
lemma dgFunctorMappingNativeComparison_horizontal :
    dgFunctorMappingHorizontal A D E B ≫ dgFunctorMappingNativeComparison A D B =
      dgFunctorTensorMappingNativeComparison A D E B ≫
        dgFunctorNativeMappingHorizontal A D E B := by
  ext n x
  apply Subtype.ext
  exact congrArg (fun f => (f.app n) x.val)
    (dgCoherentComparison_naturality (dgFunctorHorizontalDG A D E B))

end SerrePositivity.KST.SConstruction
