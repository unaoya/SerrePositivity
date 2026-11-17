module

public import SerrePositivity.EInfinity.BarrattEccles.Modules.RawModuleCofibrancy
public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.ModelHammockLocalization

/-!
# 実加群モデルへの既存 frame・局所化の特殊化

概要：M10/C02 の同じ通常加群モデルから、実分解と frame の入力を放電する。
方針：構成済み N01 の生成性を既存の関手的分解・Reedy frame・hammock 比較へ代入する。
規約：HA §1.3.4 のモデルからの underlying ∞ 圏の成分。
使われ方：通常 nerve と同じ半自由 dg nerve の指定源の比較。
注意：ここでの通常圏の宇宙表示は既存の AsSmall。元の ULiftHom 源との比較は別に行う。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory _root_.HomotopicalAlgebra
open SerrePositivity.Reedy
open _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization
open SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
variable (A : Type u) [CommRing A]

/-- 概要：同じ実自由 I による全射族の関手的分解。
方針：構成済みモデルの生成性から選ぶ。
規約：HA §1.3.4、存在仮定を追加しない。使われ方：同じ source frame。 -/
def strictRawModuleCofibrantFactorization (X : (operad A).Algebra) :
    let := strictRawModuleModelCategory A X
    MorphismProperty.FunctorialFactorizationData (cofibrations (strictRawModuleCategory A X))
      (trivialFibrations (strictRawModuleCategory A X)) := by
  let := strictRawModuleModelCategory A X
  have := strictRawModuleModelCategory_cofibrantlyGenerated A X
  have := SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.hasFunctorialFactorization_cofibration_trivialFibration
    (strictRawModuleGeneratingCofibrations A X) (strictRawModuleGeneratingTrivialCofibrations A X)
  exact MorphismProperty.functorialFactorizationData _ _

/-- 概要：同じ実自由 J による全射族の第二関手的分解。
方針：同じ構成済みモデルの生成性から選ぶ。
規約：HA §1.3.4、元の W/F。使われ方：同じ right frame。 -/
def strictRawModuleFibrantFactorization (X : (operad A).Algebra) :
    let := strictRawModuleModelCategory A X
    MorphismProperty.FunctorialFactorizationData (trivialCofibrations (strictRawModuleCategory A X))
      (fibrations (strictRawModuleCategory A X)) := by
  let := strictRawModuleModelCategory A X
  have := strictRawModuleModelCategory_cofibrantlyGenerated A X
  have := SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.hasFunctorialFactorization_trivialCofibration_fibration
    (strictRawModuleGeneratingCofibrations A X) (strictRawModuleGeneratingTrivialCofibrations A X)
  exact MorphismProperty.functorialFactorizationData _ _

/-- 概要：同じ実モデルの source frame の全関手族。
方針：実第一分解を既存 Reedy 構成へ代入する。
規約：HA §1.3.4、全対象・全射に一つの選択。使われ方：元の局所化の比較。 -/
def strictRawModuleSourceFrameFamily (X : (operad A).Algebra) :
    let := strictRawModuleModelCategory A X
    CofibrantResolutionFamily (C := strictRawModuleCategory A X) simplex := by
  let := strictRawModuleModelCategory A X
  exact cosimplicialResolutionFamily (strictRawModuleCofibrantFactorization A X)

/-- 概要：同じ実モデルの right frame の全関手族。
方針：実第二分解を既存の反対化と Reedy 構成へ代入する。
規約：HA §1.3.4、全対象・全射。使われ方：同じ全 Hom の比較。 -/
def strictRawModuleRightFrameFamily (X : (operad A).Algebra) :
    let := strictRawModuleModelCategory A X
    CofibrantResolutionFamily (C := (strictRawModuleCategory A X)ᵒᵖ) simplex := by
  let := strictRawModuleModelCategory A X
  exact SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightFrameFamilyOfFactorization
    (strictRawModuleFibrantFactorization A X)

/-- 概要：同じ全加群モデルの実 hammock は全標的の ∞ 局所化。
方針：既存の全圏普遍性に実第一分解と同じ right frame を代入する。
規約：HA §1.3.4、AsSmall 表示を保持。使われ方：元の ULiftHom 源への輸送。 -/
lemma strictRawModuleModelHammock_isLocalization (X : (operad A).Algebra) :
    let := strictRawModuleModelCategory A X
    IsLocalization
      (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.hammockLocalizationNerveMap
        (SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeCategory
          (strictRawModuleCategory A X)))
      (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.weakNerveEdges
        (SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeCategory
          (strictRawModuleCategory A X))) := by
  let := strictRawModuleModelCategory A X
  have : (cofibrations (strictRawModuleCategory A X)).HasFunctorialFactorization
      (trivialFibrations (strictRawModuleCategory A X)) :=
    ⟨⟨strictRawModuleCofibrantFactorization A X⟩⟩
  exact _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.modelHammock_isLocalization (strictRawModuleRightFrameFamily A X)

end SerrePositivity.EInfinity.BarrattEccles
