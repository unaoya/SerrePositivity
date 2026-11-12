module
public import SerrePositivity.KST.SConstruction.DGFunctorNativeMappingComparison
public import SerrePositivity.KST.SConstruction.DGNerveTensorCore

/-! # native Kan 写像空間の直積からの実 dg 横合成
概要：非離散な native core の直積から、元の全次数 dg 横合成を構成する。
方針：元の Serre 対角による core tensor 比較の後に、元の tensor dg 横合成を適用する。
規約：元の全高次入力を保持し、tensor core を直積と同一視しない。
使われ方：厳密 dg 圏の単体的豊穣入力の合成。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory Opposite SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open scoped Simplicial
variable (A : Type u) [CommRing A] (D E B : Type v)
  [DGCategory A D] [DGCategory A E] [DGCategory A B] [Small.{u} D]

/-- 元の厳密 dg 関手を native Kan 写像空間の頂点として保持する。 -/
def dgFunctorNativeMappingVertex (F : DGFunctor A D E) :
    (dgFunctorNativeMappingSpace A D E).obj (op ⦋0⦌) :=
  ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex F, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore_vertex _⟩

/-- DK/native core 比較は、元の同じ厳密 dg 関手の頂点を回収する。 -/
lemma dgFunctorMappingNativeComparison_vertex (F : DGFunctor A D E) :
    (dgFunctorMappingNativeComparison A D E).app (op ⦋0⦌) (dgFunctorMappingVertex A D E F) =
      dgFunctorNativeMappingVertex A D E F := by
  apply Subtype.ext
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertexEquiv.injective
  rfl

variable [Small.{u} E]

/-- 元の native Kan 写像空間の直積から、実 tensor source の native core への射。 -/
def dgFunctorNativeTensorComparison :
    dgFunctorNativeMappingSpace A D E ⊗ dgFunctorNativeMappingSpace A E B ⟶
      dgFunctorNativeTensorMappingSpace A D E B :=
  dgNerveCoreTensor A (DGFunctor A D E) (DGFunctor A E B)

/-- 元の native Kan 写像空間の直積からの、全次数を保持する実横合成。 -/
def dgFunctorNativeComposition :
    dgFunctorNativeMappingSpace A D E ⊗ dgFunctorNativeMappingSpace A E B ⟶
      dgFunctorNativeMappingSpace A D B :=
  dgFunctorNativeTensorComparison A D E B ≫ dgFunctorNativeMappingHorizontal A D E B

/-- 元の native 横合成は、厳密 dg 関手の元の合成を頂点として回収する。 -/
lemma dgFunctorNativeComposition_vertex (F : DGFunctor A D E) (G : DGFunctor A E B) :
    (dgFunctorNativeComposition A D E B).app (op ⦋0⦌)
        (dgFunctorNativeMappingVertex A D E F, dgFunctorNativeMappingVertex A E B G) =
      dgFunctorNativeMappingVertex A D B (DGFunctor.comp F G) := by
  apply Subtype.ext
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertexEquiv.injective
  rfl

/-- 既存 DK 写像空間の直積から実 tensor source の native core への比較。 -/
def dgFunctorMappingTensorNativeComparison :
    dgFunctorMappingSpace A D E ⊗ dgFunctorMappingSpace A E B ⟶
      dgFunctorNativeTensorMappingSpace A D E B :=
  (dgFunctorMappingNativeComparison A D E ⊗ₘ dgFunctorMappingNativeComparison A E B) ≫
    dgFunctorNativeTensorComparison A D E B

/-- DK からの tensor 比較と native 横合成は、同じ二つの native 入力の合成を回収する。 -/
lemma dgFunctorMappingTensorNativeComparison_composition :
    dgFunctorMappingTensorNativeComparison A D E B ≫ dgFunctorNativeMappingHorizontal A D E B =
      (dgFunctorMappingNativeComparison A D E ⊗ₘ dgFunctorMappingNativeComparison A E B) ≫
        dgFunctorNativeComposition A D E B := by
  exact Category.assoc _ _ _

end SerrePositivity.KST.SConstruction
