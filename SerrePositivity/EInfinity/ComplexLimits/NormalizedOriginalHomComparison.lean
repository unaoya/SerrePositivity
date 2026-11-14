module

public import SerrePositivity.EInfinity.ComplexLimits.NormalizedProbeHomKan
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
namespace SerrePositivity.EInfinity.ComplexLimits
open CategoryTheory HomotopicalAlgebra SSet
open SerrePositivity.DifferentialGraded SerrePositivity.Reedy
open SerrePositivity.HomotopyFunctionComplex SerrePositivity.InfinityCategories

variable (A : Type u) [CommRing A]

def normalizedOriginalHomRestriction :
    BarrattEccles.complexSourceFrameHom A ⟶ normalizedProbeStandardHom A := by
  let := projectiveModelCategory A
  exact _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.resolutionHomSourceRestriction
    (cosimplicialResolutionFamily (mappingCofibrantFactorization A))
    (framedLimitProbeFunctor A) (framedLimitProbeComparisonNatTrans A) (𝟭 (Complex A))

def normalizedOriginalHomComparison :
    BarrattEccles.complexSourceFrameHom A ⟶ normalizedProbeHomMiddle A :=
  normalizedOriginalHomRestriction A ≫ normalizedProbeHomFromStandard A

lemma normalizedOriginalHom_kanComplex (X : (Complex A)ᵒᵖ) (Y : Complex A) :
    KanComplex (((BarrattEccles.complexSourceFrameHom A).obj X).obj Y) := by
  let := projectiveModelCategory A
  have := BarrattEccles.CarrierDiagram.complex_isFibrant A Y
  let q := cosimplicialResolutionFamily (mappingCofibrantFactorization A)
  exact cosimplicialHom_kanComplex _ (q.cofibrant X.unop)
    (q.atObject X.unop).homotopicallyConstant Y

lemma normalizedOriginalHomRestriction_homotopyEquivalence
    (X : (Complex A)ᵒᵖ) (Y : Complex A) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (((normalizedOriginalHomRestriction A).app X).app Y) := by
  let := projectiveModelCategory A
  letI : CategoryTheory.Limits.HasLimitsOfSize.{u, u} (Complex A) := ⟨fun _ _ => inferInstance⟩
  have : IsFibrant ((𝟭 (Complex A)).obj Y) :=
    BarrattEccles.CarrierDiagram.complex_isFibrant A Y
  exact _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.resolutionHomSourceRestriction_homotopyEquivalence
    (cosimplicialResolutionFamily (mappingCofibrantFactorization A))
    (framedLimitProbeFunctor A) (framedLimitProbeComparisonNatTrans A) (𝟭 (Complex A))
    (framedLimitProbeComparison_quasiIso A) X Y

lemma normalizedOriginalHomComparison_homotopyEquivalence
    (X : (Complex A)ᵒᵖ) (Y : Complex A) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (((normalizedOriginalHomComparison A).app X).app Y) := by
  have := normalizedOriginalHom_kanComplex A X Y
  have := normalizedProbeStandardHom_kanComplex A X Y
  have := normalizedProbeHomMiddle_kanComplex A X Y
  exact (normalizedOriginalHomRestriction_homotopyEquivalence A X Y).comp
    (normalizedProbeHomFromStandard_homotopyEquivalence A X Y)

end SerrePositivity.EInfinity.ComplexLimits
