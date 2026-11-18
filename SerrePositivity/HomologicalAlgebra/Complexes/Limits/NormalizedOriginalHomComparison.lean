module

public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.NormalizedProbeHomKan
public import SerrePositivity.EInfinity.BarrattEccles.FreeForgetHomFrames
public import SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MappingSpaces.ResolutionHomSourceRestriction

/-!
# 元の始域を持つ標準 Hom から正規化共通 Hom への比較

概要：元の始域置換の比較に沿う前合成を、同じ probe の実 Hom span に接続する。
方針：既存の全二変数自然変換と構成した実ホモトピー同値を合成する。
規約：元の標準 source frame と同じ始域・標的を保つ。
使われ方：元の自由忘却 Hom 比較と実 Dold–Kan Hom の接続。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.ComplexLimits
open _root_.CategoryTheory _root_.HomotopicalAlgebra _root_.SSet
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.Reedy
open _root_.SerrePositivity.HomotopyFunctionComplex _root_.SerrePositivity.InfinityCategories

variable (A : Type u) [CommRing A]

def normalizedOriginalHomRestriction :
    _root_.SerrePositivity.EInfinity.BarrattEccles.complexSourceFrameHom A ⟶ _root_.SerrePositivity.ComplexLimits.normalizedProbeStandardHom A := by
  let := _root_.SerrePositivity.ProjectiveModel.projectiveModelCategory A
  exact _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.resolutionHomSourceRestriction
    (cosimplicialResolutionFamily (_root_.SerrePositivity.ComplexLimits.mappingCofibrantFactorization A))
    (_root_.SerrePositivity.ComplexLimits.framedLimitProbeFunctor A) (_root_.SerrePositivity.ComplexLimits.framedLimitProbeComparisonNatTrans A) (𝟭 (Complex A))

def normalizedOriginalHomComparison :
    _root_.SerrePositivity.EInfinity.BarrattEccles.complexSourceFrameHom A ⟶ _root_.SerrePositivity.ComplexLimits.normalizedProbeHomMiddle A :=
  _root_.SerrePositivity.ComplexLimits.normalizedOriginalHomRestriction A ≫ _root_.SerrePositivity.ComplexLimits.normalizedProbeHomFromStandard A

lemma normalizedOriginalHom_kanComplex (X : (Complex A)ᵒᵖ) (Y : Complex A) :
    KanComplex (((_root_.SerrePositivity.EInfinity.BarrattEccles.complexSourceFrameHom A).obj X).obj Y) := by
  let := _root_.SerrePositivity.ProjectiveModel.projectiveModelCategory A
  have := _root_.SerrePositivity.EInfinity.BarrattEccles.CarrierDiagram.complex_isFibrant A Y
  let q := cosimplicialResolutionFamily (_root_.SerrePositivity.ComplexLimits.mappingCofibrantFactorization A)
  exact cosimplicialHom_kanComplex _ (q.cofibrant X.unop)
    (q.atObject X.unop).homotopicallyConstant Y

lemma normalizedOriginalHomRestriction_homotopyEquivalence
    (X : (Complex A)ᵒᵖ) (Y : Complex A) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (((_root_.SerrePositivity.ComplexLimits.normalizedOriginalHomRestriction A).app X).app Y) := by
  let := _root_.SerrePositivity.ProjectiveModel.projectiveModelCategory A
  letI : CategoryTheory.Limits.HasLimitsOfSize.{u, u} (Complex A) := ⟨fun _ _ => inferInstance⟩
  have : IsFibrant ((𝟭 (Complex A)).obj Y) :=
    _root_.SerrePositivity.EInfinity.BarrattEccles.CarrierDiagram.complex_isFibrant A Y
  exact _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.resolutionHomSourceRestriction_homotopyEquivalence
    (cosimplicialResolutionFamily (_root_.SerrePositivity.ComplexLimits.mappingCofibrantFactorization A))
    (_root_.SerrePositivity.ComplexLimits.framedLimitProbeFunctor A) (_root_.SerrePositivity.ComplexLimits.framedLimitProbeComparisonNatTrans A) (𝟭 (Complex A))
    (_root_.SerrePositivity.ComplexLimits.framedLimitProbeComparison_quasiIso A) X Y

lemma normalizedOriginalHomComparison_homotopyEquivalence
    (X : (Complex A)ᵒᵖ) (Y : Complex A) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (((_root_.SerrePositivity.ComplexLimits.normalizedOriginalHomComparison A).app X).app Y) := by
  have := _root_.SerrePositivity.ComplexLimits.normalizedOriginalHom_kanComplex A X Y
  have := _root_.SerrePositivity.ComplexLimits.normalizedProbeStandardHom_kanComplex A X Y
  have := _root_.SerrePositivity.ComplexLimits.normalizedProbeHomMiddle_kanComplex A X Y
  exact (_root_.SerrePositivity.ComplexLimits.normalizedOriginalHomRestriction_homotopyEquivalence A X Y).comp
    (_root_.SerrePositivity.ComplexLimits.normalizedProbeHomFromStandard_homotopyEquivalence A X Y)

end SerrePositivity.ComplexLimits
