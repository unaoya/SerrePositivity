module

public import SerrePositivity.EInfinity.BarrattEccles.FreeForgetHomKan
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.DiscreteComparison

/-!
# 実自由忘却 Hom span の両射のホモトピー同値性

概要：元の全二変数比較射自身が共に実単体的ホモトピー同値である。
方針：固定 Quillen frame 比較と元の probe augmentation の解消前合成を使う。
規約：元の標的代数・元の忘却・同じ共通始域比較を保持する。
使われ方：同じ U の ∞ 随伴の写像空間比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory HomotopicalAlgebra SSet
open SerrePositivity.DifferentialGraded SerrePositivity.Reedy
open SerrePositivity.HomotopyFunctionComplex
open SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A]

lemma freeHomFromLeft_homotopyEquivalence (X : (Complex A)ᵒᵖ) (B : (operad A).Algebra) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (((freeHomFromLeft A).app X).app B) := by
  let := projectiveModelCategory A
  let := modelCategory A
  have := free_isLeftQuillen A
  have := isFibrant A B
  exact _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.quillenLeftFrameCommon_left_homotopyEquivalence (operad A).freeAlgebraFunctor
    (CosimplicialFrameFamily.ofResolution
      (cosimplicialResolutionFamily (carrierProbeFactorization A)))
    (ComplexLimits.framedLimitProbeFunctor A) (ComplexLimits.framedLimitProbe_cofibrant A)
    (mappingCofibrantFactorization A)
    (cosimplicialResolutionFamily (mappingCofibrantFactorization A)) X B

lemma freeHomFromRight_homotopyEquivalence (X : (Complex A)ᵒᵖ) (B : (operad A).Algebra) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (((freeHomFromRight A).app X).app B) := by
  let := projectiveModelCategory A
  letI : CategoryTheory.Limits.HasLimitsOfSize.{u, u} (Complex A) := ⟨fun _ _ => inferInstance⟩
  let := modelCategory A
  have := free_isLeftQuillen A
  have := (operad A).freeAlgebraAdjunction.isLeftAdjoint
  have := (operad A).freeAlgebraAdjunction.isRightAdjoint
  have := forget_isRightQuillen A
  have := isFibrant A B
  have : IsFibrant ((Operad.Algebra.forget (operad A)).obj B) :=
    SerrePositivity.Quillen.isFibrant_obj
    (Operad.Algebra.forget (operad A)) B
  let qC := cosimplicialResolutionFamily (carrierProbeFactorization A)
  let Q := ComplexLimits.framedLimitProbeFunctor A
  let ε := ComplexLimits.framedLimitProbeComparisonNatTrans A
  let P := CosimplicialFrameFamily.ofResolution qC
  let e := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.adjunctionFrameHomBifunctorIso (operad A).freeAlgebraAdjunction
    (Q ⋙ qC.obj) (𝟭 (operad A).Algebra)
  have hε : ∀ X, weakEquivalences (Complex A) (ε.app X) :=
    ComplexLimits.framedLimitProbeComparison_quasiIso A
  have h1 := _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.resolutionHomSourceRestriction_homotopyEquivalence qC Q ε
    (Operad.Algebra.forget (operad A)) hε X B
  have h2 := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.homotopyEquivalence_of_isIso ((e.inv.app X).app B)
  have h3 := _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.quillenLeftFrameCommon_right_homotopyEquivalence (operad A).freeAlgebraFunctor
    P Q (ComplexLimits.framedLimitProbe_cofibrant A) (mappingCofibrantFactorization A)
    (cosimplicialResolutionFamily (mappingCofibrantFactorization A)) X B
  have : KanComplex (((qC.obj.op ⋙ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHomBifunctor ⋙
      (Functor.whiskeringLeft (operad A).Algebra (Complex A) SSet.{u}).obj
        (Operad.Algebra.forget (operad A))).obj X).obj B) := freeHomRight_kanComplex A X B
  have : KanComplex (((((Q ⋙ qC.obj).op ⋙ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHomBifunctor ⋙
      (Functor.whiskeringLeft (operad A).Algebra (Complex A) SSet.{u}).obj
        (Operad.Algebra.forget (operad A))).obj X).obj B)) :=
    freeHomRight_kanComplex A (Opposite.op (Q.obj X.unop)) B
  have : KanComplex (((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.adjunctionRightFrameHom (R := Operad.Algebra.forget (operad A))
      (Q ⋙ qC.obj) (𝟭 (operad A).Algebra)).obj X).obj B) :=
    freeHomRight_kanComplex A (Opposite.op (Q.obj X.unop)) B
  have : KanComplex (((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.adjunctionLeftFrameHom (L := (operad A).freeAlgebraFunctor)
      (Q ⋙ qC.obj) (𝟭 (operad A).Algebra)).obj X).obj B) :=
    cosimplicialHom_kanComplex _
      (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.quillenReplacedFrame_reedyCofibrant (operad A).freeAlgebraAdjunction P Q X.unop)
      (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.quillenReplacedFrame_homotopicallyConstant P Q X.unop) B
  have := freeHomMiddle_kanComplex A X B
  exact h1.comp (h2.comp h3)

end SerrePositivity.EInfinity.BarrattEccles
