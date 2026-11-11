module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.GeneratedArrows
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.CoreCoconeLeg

/-!
概要：固定した元の始域から強飽和生成閉包に属する辺の、全 coslice 部分圏を構成する。
方針：元の一点下の coslice の脚を条件にし、同じ始域・終域を持つ辺を回収する。
規約：この圏の presentable 性・終対象・局所置換の存在はまだ主張しない。
使われ方：P-1 f3、HTT 5.5.5.14 の終対象構成の標的。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
variable {C : SSet.{u + 1}} [Quasicategory C] {I : Type u}

/-- 指定された元の始域から、生成閉包に属する脚を持つ全 coslice 部分圏。 -/
def generatedSourceCategory (edges : I → C _⦋1⦌) (x : C _⦋0⦌) : SSet.{u + 1} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (SSet.yonedaEquiv.symm x))
    (fun c ↦ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone.leg c (𝟙 Δ[0])).edge ∈ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.generatedEdges edges)

instance generatedSourceCategory_quasicategory (edges : I → C _⦋1⦌) (x : C _⦋0⦌) :
    Quasicategory (generatedSourceCategory edges x) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.InnerFibrations.fullSubcomplexOnVertices_quasicategory _ _

/-- 固定始域の全 coslice 圏への全部分包含。 -/
def generatedSourceInclusion (edges : I → C _⦋1⦌) (x : C _⦋0⦌) :
    generatedSourceCategory edges x ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (SSet.yonedaEquiv.symm x) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (SSet.yonedaEquiv.symm x))
    (fun c ↦
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone.leg c (𝟙 Δ[0])).edge ∈ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.generatedEdges edges)).ι

/-- 元の標的圏に終域を返す射影。 -/
def generatedSourceTarget (edges : I → C _⦋1⦌) (x : C _⦋0⦌) :
    generatedSourceCategory edges x ⟶ C :=
  generatedSourceInclusion edges x ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (SSet.yonedaEquiv.symm x)

/-- coslice 圏への包含は元の全写像空間を保持する。 -/
lemma generatedSourceInclusion_isFullyFaithful (edges : I → C _⦋1⦌) (x : C _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful (generatedSourceInclusion edges x) := by
  exact _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.isFullyFaithful_fullSubcomplexOnVertices_ι _ _

/-- 元の指定始域を始点として厳密に保持する、固定始域圏の各頂点の実際の辺。 -/
def generatedSourceLeg (edges : I → C _⦋1⦌) (x : C _⦋0⦌)
    (t : (generatedSourceCategory edges x) _⦋0⦌) :
    Truncated.Edge (X := (truncation 2).obj C) x ((generatedSourceTarget edges x).app _ t) where
  edge := (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone.leg t.val (𝟙 Δ[0])).edge
  src_eq := by
    change C.δ 1 (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone.leg t.val (𝟙 Δ[0])).edge = x
    have h := (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone.leg t.val (𝟙 Δ[0])).src_eq
    change C.δ 1 (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone.leg t.val (𝟙 Δ[0])).edge =
      SSet.yonedaEquiv (𝟙 Δ[0] ≫ SSet.yonedaEquiv.symm x) at h
    simpa only [Category.id_comp, Equiv.apply_symm_apply] using h
  tgt_eq := by
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone.leg t.val (𝟙 Δ[0])).tgt_eq

/-- 回収した元の指定始域の辺は、元の強飽和生成閉包に属する。 -/
lemma generatedSourceLeg_mem (edges : I → C _⦋1⦌) (x : C _⦋0⦌)
    (t : (generatedSourceCategory edges x) _⦋0⦌) :
    (generatedSourceLeg edges x t).edge ∈ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.generatedEdges edges :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex t

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
