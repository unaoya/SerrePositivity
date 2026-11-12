module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.FiniteProductPreservation
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.PresheafInfinity
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.InnerFibrations.FullSubcomplexFibration
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FullSubcomplexMapping

/-!
概要：有限余積を積へ送る前層の ∞ 圏 P_Σ(C)。
方針：元の P(C) の頂点が表す反変関手の有限積保存を頂点条件に取る。
規約：有限積条件は Cᵒᵖ の元の全極限錐を使う。反射や局所化の存在は仮定しない。
使われ方：HTT 5.5.8.8、Yoneda の因子化と sifted 余極限での閉性。

対応節は Kerodon 9.7（Tag 06ZD）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories

/-- 前層の元の反変関手が、有限余積を積へ送る条件。 -/
def IsSigmaPresheaf {C : SSet.{u}} (F : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.PresheafInfinity C) _⦋0⦌) : Prop :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.PreservesFiniteProductsFromSmallSource ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.presheafInfinityObjectEquiv C).symm F)

/-- 元の反変関手を頂点表示したとき、P_Σ の条件は元の関手の有限積保存。 -/
lemma isSigmaPresheaf_object_iff {C : SSet.{u}}
    (F : (SSet.uliftFunctor.{u + 1, u}).obj C.op ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}) :
    IsSigmaPresheaf (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.presheafInfinityObjectEquiv C F) ↔
      _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.PreservesFiniteProductsFromSmallSource F := by
  simp only [IsSigmaPresheaf, Equiv.symm_apply_apply]

/-- 有限余積を積へ送る前層の、元の P(C) 内の全部分複体。 -/
def sigmaPresheavesSubcomplex (C : SSet.{u}) : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.PresheafInfinity C).Subcomplex :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.PresheafInfinity C) IsSigmaPresheaf

/-- HTT 5.5.8.8 の P_Σ(C)。有限余積を持つ C の前層の全部分 ∞ 圏。 -/
def SigmaPresheafInfinity (C : SSet.{u}) : SSet.{u + 1} := sigmaPresheavesSubcomplex C

/-- P_Σ(C) は元の前層 ∞ 圏の全部分 quasicategory。 -/
instance sigmaPresheafInfinity_quasicategory (C : SSet.{u}) :
    Quasicategory (SigmaPresheafInfinity C) :=
  inferInstanceAs (Quasicategory
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.PresheafInfinity C) IsSigmaPresheaf : SSet.{u + 1}))

/-- P_Σ(C) から元の前層 ∞ 圏への包含。 -/
def sigmaPresheafInfinityInclusion (C : SSet.{u}) :
    SigmaPresheafInfinity C ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.PresheafInfinity C := (sigmaPresheavesSubcomplex C).ι

/-- 包含は元の写像空間で充満忠実。 -/
lemma sigmaPresheafInfinityInclusion_isFullyFaithful (C : SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful (sigmaPresheafInfinityInclusion C) :=
  _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.isFullyFaithful_fullSubcomplexOnVertices_ι _ _

/-- P_Σ の対象は、元の前層の有限余積から積への保存条件を満たす。 -/
lemma sigmaPresheafInfinity_vertex {C : SSet.{u}}
    (F : (SigmaPresheafInfinity C) _⦋0⦌) :
    IsSigmaPresheaf ((sigmaPresheafInfinityInclusion C).app (Opposite.op ⦋0⦌) F) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex F

/-- P_Σ の対象条件は元の前層 ∞ 圏での対象同型に関して不変。 -/
lemma isSigmaPresheaf_iff_of_vertexIso {C : SSet.{u}}
    {F G : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.PresheafInfinity C) _⦋0⦌} (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso F G) :
    IsSigmaPresheaf F ↔ IsSigmaPresheaf G := by
  let f := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.presheafInfinityObjectEquiv C).symm F
  let g := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.presheafInfinityObjectEquiv C).symm G
  have he : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f g := by
    have hf : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f = F := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.presheafInfinityObjectEquiv C).apply_symm_apply F
    have hg : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex g = G := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.presheafInfinityObjectEquiv C).apply_symm_apply G
    change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex g)
    rw [hf, hg]
    exact e
  exact _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.preservesFiniteProductsFromSmallSource_iff_of_functorIso he

/-- 全頂点が有限余積を積へ送る前層の族を、元の族ごと P_Σ へ制限する。 -/
def sigmaPresheafInfinityLift {A : SSet.{u + 1}} {C : SSet.{u}}
    (F : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.PresheafInfinity C)
    (hF : ∀ a : A _⦋0⦌, IsSigmaPresheaf (F.app (Opposite.op ⦋0⦌) a)) :
    A ⟶ SigmaPresheafInfinity C := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift IsSigmaPresheaf F hF

/-- 族の P_Σ への制限は、包含後に元の全 ∞ 関手を厳密に回収する。 -/
lemma sigmaPresheafInfinityLift_inclusion {A : SSet.{u + 1}} {C : SSet.{u}}
    (F : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.PresheafInfinity C)
    (hF : ∀ a : A _⦋0⦌, IsSigmaPresheaf (F.app (Opposite.op ⦋0⦌) a)) :
    sigmaPresheafInfinityLift F hF ≫ sigmaPresheafInfinityInclusion C = F :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift_ι _ _ _

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories
