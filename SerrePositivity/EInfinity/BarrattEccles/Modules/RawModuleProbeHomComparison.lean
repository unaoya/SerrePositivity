module

public import SerrePositivity.EInfinity.BarrattEccles.Modules.RawModuleProbeCommonFrame
public import SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Frames.FixedQuillenFrameComparison

/-!
# 同じ二つの加群 frame Hom の実高次比較

概要：M10 の二変数自然な同じ比較射の両脚をホモトピー同値と証明する。
方針：既存の固定 Quillen 類での frame 不変性に実 frame 条件を渡す。
規約：HA §1.3.4、単体集合のモデルを仮定せず、全標的の実 Hom 射を保持する。
使われ方：選択済みモデル frame Hom から元の dg Hom への比較。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory _root_.HomotopicalAlgebra
open SerrePositivity.HomotopyFunctionComplex
open SerrePositivity.InfinityCategories.HA.Section7_1_1
open SerrePositivity.InfinityCategories.Project.ModelCategoryComparison
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes
open TheHomotopyTheoryOfKanComplexes
variable (A : Type u) [CommRing A]

/-- 概要：元の標準 Hom から同じ共通 Hom への同じ比較はホモトピー同値。
方針：同じ augmentation と実モデルを固定 frame 不変性へ渡す。
規約：HA §1.3.4、全 probe と任意の標的。使われ方：標準側の比較の放電。 -/
lemma strictRawModuleProbeHomFromStandard_homotopyEquivalence (X : (operad A).Algebra)
    (P : (strictRawModuleProbeCategory A X)ᵒᵖ) (N : strictRawModuleCategory A X) :
    IsSimplicialHomotopyEquivalence (((strictRawModuleProbeHomFromStandard A X).app P).app N) := by
  let := strictRawModuleModelCategory A X
  have := strictRawModuleModelCategory_allFibrant A X N
  exact fixedFrameOverFunctor_homLeft_homotopyEquivalence
    (strictRawModuleCofibrantFactorization A X) (strictRawModuleSourceFrameFamily A X)
    (strictRawModuleProbeFunctor A X) (strictRawModuleProbeTensorFrame A X)
    (strictRawModuleProbeTensorAugmentation A X) (strictRawModuleProbeTensorAugmentation_weak A X) P N

/-- 概要：元のテンソル Hom から同じ共通 Hom への同じ比較はホモトピー同値。
方針：同じ Reedy 条件・定数性・augmentation で固定 frame 不変性を使う。
規約：HA §1.3.4、全単体の比較。使われ方：dg Hom 側の比較の放電。 -/
lemma strictRawModuleProbeHomFromTensor_homotopyEquivalence (X : (operad A).Algebra)
    (P : (strictRawModuleProbeCategory A X)ᵒᵖ) (N : strictRawModuleCategory A X) :
    IsSimplicialHomotopyEquivalence (((strictRawModuleProbeHomFromTensor A X).app P).app N) := by
  let := strictRawModuleModelCategory A X
  have := strictRawModuleModelCategory_allFibrant A X N
  exact fixedFrameOverFunctor_homRight_homotopyEquivalence
    (strictRawModuleCofibrantFactorization A X) (strictRawModuleSourceFrameFamily A X)
    (strictRawModuleProbeFunctor A X) (strictRawModuleProbeTensorFrame A X)
    (strictRawModuleProbeTensorAugmentation A X) (strictRawModuleProbeTensorAugmentation_weak A X)
    (strictRawModuleProbeTensorFrame_cofibrant A X)
    (strictRawModuleProbeTensorFrame_homotopicallyConstant A X) P N

/-- 概要：元の標準 frame の同じ全 Hom は Kan。
方針：N01 の同じ選択済み frame と全標的の fibrancy を使う。
規約：HA §1.3.4、元の単体集合。使われ方：Kan 比較の標準端点。 -/
lemma strictRawModuleProbeStandardHom_kanComplex (X : (operad A).Algebra)
    (P : (strictRawModuleProbeCategory A X)ᵒᵖ) (N : strictRawModuleCategory A X) :
    SSet.KanComplex (((strictRawModuleProbeStandardHom A X).obj P).obj N) := by
  let := strictRawModuleModelCategory A X
  have := strictRawModuleModelCategory_allFibrant A X N
  exact cosimplicialHom_kanComplex _
    ((strictRawModuleSourceFrameFamily A X).cofibrant ((strictRawModuleProbeFunctor A X).obj P.unop))
    ((strictRawModuleSourceFrameFamily A X).atObject
      ((strictRawModuleProbeFunctor A X).obj P.unop)).homotopicallyConstant N

/-- 概要：元のテンソル frame の同じ全 Hom は Kan。
方針：同じ半自由 probe の検証済み Kan 条件を使う。
規約：HA §1.3.4、元の単体集合。使われ方：Kan 比較の dg Hom 側端点。 -/
lemma strictRawModuleProbeTensorHom_kanComplex (X : (operad A).Algebra)
    (P : (strictRawModuleProbeCategory A X)ᵒᵖ) (N : strictRawModuleCategory A X) :
    SSet.KanComplex (((strictRawModuleProbeTensorHom A X).obj P).obj N) :=
  strictRawModuleTensorHom_kanComplex A X ((strictRawModuleProbeFunctor A X).obj P.unop) N
    (strictRawModuleProbeFunctor_semifree A X P.unop)

/-- 概要：同じ共通 frame の同じ全 Hom は Kan。
方針：実共通置換の Reedy 条件と同じ augmentation の定数性を使う。
規約：HA §1.3.4、全標的。使われ方：Kan 比較の共通標的。 -/
lemma strictRawModuleProbeCommonHom_kanComplex (X : (operad A).Algebra)
    (P : (strictRawModuleProbeCategory A X)ᵒᵖ) (N : strictRawModuleCategory A X) :
    SSet.KanComplex (((strictRawModuleProbeCommonHom A X).obj P).obj N) := by
  let := strictRawModuleModelCategory A X
  have := strictRawModuleModelCategory_allFibrant A X N
  exact cosimplicialHom_kanComplex _
    (strictRawModuleProbeCommonFrame_cofibrant A X P.unop)
    (strictRawModuleProbeCommonFrame_homotopicallyConstant A X P.unop) N

end SerrePositivity.EInfinity.BarrattEccles
