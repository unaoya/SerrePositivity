module
public import SerrePositivity.KST.SConstruction.DGStandardCoherentMap
public import SerrePositivity.KST.SConstruction.DGFunctorHorizontalDG
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CoreKan

/-! # 厳密 dg 関手圏の非離散な core 写像空間
概要：全次数 dg 関手圏の標準 DK coherent nerve の core を、Kan 写像空間として作る。
方針：元の dg 前後合成と tensor 横合成へ γ1 を適用し、core に制限する。
規約：関手を頂点に持ち、可逆な高次比較を保持する。使われ方：厳密 dg 入力の構成。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories

open scoped Simplicial
variable (A : Type u) [CommRing A] (D E B : Type v)
  [DGCategory A D] [DGCategory A E] [DGCategory A B] [Small.{u} D]

/-- 全次数 dg 関手圏の標準 DK coherent nerve の core。 -/
def dgFunctorMappingSpace : SSet.{max u v} :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.doldKanCoherentNerve (R := A) (D := DGFunctor A D E)) : SSet)

/-- 元の非離散な dg 関手の core 写像空間は Kan 複体。 -/
instance dgFunctorMappingSpace_kan : KanComplex (dgFunctorMappingSpace A D E) := by
  change KanComplex
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.doldKanCoherentNerve (R := A) (D := DGFunctor A D E)) : SSet)
  infer_instance

/-- 元の dg 関手を core 写像空間の頂点として保持する。 -/
def dgFunctorMappingVertex (F : DGFunctor A D E) :
    (dgFunctorMappingSpace A D E).obj (Opposite.op ⦋0⦌) :=
  ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (ForgetEnrichment.of (Complex A) F), _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore_vertex _⟩

/-- core 写像空間の頂点は、元の厳密 dg 関手そのものである。 -/
def dgFunctorMappingVertexEquiv :
    DGFunctor A D E ≃ (dgFunctorMappingSpace A D E).obj (Opposite.op ⦋0⦌) where
  toFun := dgFunctorMappingVertex A D E
  invFun x := ForgetEnrichment.to (Complex A) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveObject x.val)
  left_inv _ := rfl
  right_inv x := Subtype.ext (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex_object x.val)

/-- core 写像空間から元の全次数 dg 関手圏の標準 DK coherent nerve への包含。 -/
def dgFunctorMappingInclusion :
    dgFunctorMappingSpace A D E ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.doldKanCoherentNerve (R := A) (D := DGFunctor A D E) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore _).ι

/-- 元の厳密 dg 後合成による非離散な写像空間の射。 -/
def dgFunctorMappingPost (H : DGFunctor A E B) :
    dgFunctorMappingSpace A D E ⟶ dgFunctorMappingSpace A D B :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreMap (dgStandardCoherentMap (dgFunctorPostDG A D E B H))

/-- core 上の後合成は、包含後に元の全単体の後合成を回収する。 -/
lemma dgFunctorMappingPost_inclusion (H : DGFunctor A E B) :
    dgFunctorMappingPost A D E B H ≫ dgFunctorMappingInclusion A D B =
      dgFunctorMappingInclusion A D E ≫
        dgStandardCoherentMap (dgFunctorPostDG A D E B H) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreMap_ι _

/-- core 上の後合成は、元の厳密 dg 関手の合成を頂点として回収する。 -/
lemma dgFunctorMappingPost_vertex (H : DGFunctor A E B) (F : DGFunctor A D E) :
    (dgFunctorMappingPost A D E B H).app (Opposite.op ⦋0⦌) (dgFunctorMappingVertex A D E F) =
      dgFunctorMappingVertex A D B (F.comp H) := by
  apply Subtype.ext
  exact dgStandardCoherentMap_vertex (dgFunctorPostDG A D E B H)
    (ForgetEnrichment.of (Complex A) F)

variable [Small.{u} B]

/-- 元の厳密 dg 前合成による非離散な写像空間の射。 -/
def dgFunctorMappingPre (H : DGFunctor A B D) :
    dgFunctorMappingSpace A D E ⟶ dgFunctorMappingSpace A B E :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreMap (dgStandardCoherentMap (dgFunctorPreDG A D E B H))

/-- core 上の前合成は、包含後に元の全単体の前合成を回収する。 -/
lemma dgFunctorMappingPre_inclusion (H : DGFunctor A B D) :
    dgFunctorMappingPre A D E B H ≫ dgFunctorMappingInclusion A B E =
      dgFunctorMappingInclusion A D E ≫
        dgStandardCoherentMap (dgFunctorPreDG A D E B H) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreMap_ι _

/-- core 上の前合成は、元の厳密 dg 関手の合成を頂点として回収する。 -/
lemma dgFunctorMappingPre_vertex (H : DGFunctor A B D) (F : DGFunctor A D E) :
    (dgFunctorMappingPre A D E B H).app (Opposite.op ⦋0⦌) (dgFunctorMappingVertex A D E F) =
      dgFunctorMappingVertex A B E (H.comp F) := by
  apply Subtype.ext
  exact dgStandardCoherentMap_vertex (dgFunctorPreDG A D E B H)
    (ForgetEnrichment.of (Complex A) F)

variable [Small.{u} E]

/-- tensor dg 関手圏の標準 DK coherent nerve の元の core。 -/
def dgFunctorTensorMappingSpace : SSet.{max u v} :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.doldKanCoherentNerve (R := A)
    (D := DGTensorCategory A (DGFunctor A D E) (DGFunctor A E B))) : SSet)

/-- tensor dg 関手圏の core は、非離散な Kan 複体。 -/
instance dgFunctorTensorMappingSpace_kan :
    KanComplex (dgFunctorTensorMappingSpace A D E B) := by
  change KanComplex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.doldKanCoherentNerve (R := A)
    (D := DGTensorCategory A (DGFunctor A D E) (DGFunctor A E B))) : SSet)
  infer_instance

/-- 元の関手の対を tensor dg 関手圏の core の頂点として保持する。 -/
def dgFunctorTensorMappingVertex (F : DGFunctor A D E) (G : DGFunctor A E B) :
    (dgFunctorTensorMappingSpace A D E B).obj (Opposite.op ⦋0⦌) :=
  ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (ForgetEnrichment.of
    (C := DGTensorCategory A (DGFunctor A D E) (DGFunctor A E B)) (Complex A) (F, G)),
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore_vertex _⟩

/-- 元の tensor dg 横合成に γ1 と core を適用した、Kan 複体間の射。 -/
def dgFunctorMappingHorizontal :
    dgFunctorTensorMappingSpace A D E B ⟶ dgFunctorMappingSpace A D B :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreMap (dgStandardCoherentMap (dgFunctorHorizontalDG A D E B))

omit [Small.{u} B] in
/-- tensor dg 横合成の core 作用は、元の dg 合成を頂点として回収する。 -/
lemma dgFunctorMappingHorizontal_vertex (F : DGFunctor A D E) (G : DGFunctor A E B) :
    (dgFunctorMappingHorizontal A D E B).app (Opposite.op ⦋0⦌)
        (dgFunctorTensorMappingVertex A D E B F G) =
      dgFunctorMappingVertex A D B (F.comp G) := by
  apply Subtype.ext
  exact dgStandardCoherentMap_vertex (dgFunctorHorizontalDG A D E B)
    (ForgetEnrichment.of
      (C := DGTensorCategory A (DGFunctor A D E) (DGFunctor A E B)) (Complex A) (F, G))

end SerrePositivity.KST.SConstruction
