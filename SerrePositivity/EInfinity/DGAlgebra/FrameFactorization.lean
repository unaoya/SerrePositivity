module

public import SerrePositivity.EInfinity.DGAlgebra.ModelCategory
public import SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Replacements.ModelCofibrantHammockWeak
public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.ModelHammockNerveEquivalence

/-!
概要：実 dg 代数モデルの生成射から frame 比較の関手的分解入力を放電する。
方針：同じ自由 I/J の小対象論法と生成モデルの右類の同定を使う。
規約：モデル構造と分解の instance は局所的に選び、大域 instance にしない。
使われ方：Sp への追加仮定の残らない cofibrant 部分圏と全 dg 代数の比較。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.EInfinity.DGAlgebra
open CategoryTheory _root_.HomotopicalAlgebra
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization
variable (R : Type u) [CommRing R]

/-- 概要：実自由生成 cofibration の小対象論法は第一の関手的分解を与える。
方針：同じモデルの生成性を一般の関手的分解定理へ渡す。
規約：実モデルを局所選択する。使われ方：全 dg 代数の cofibrant 置換。 -/
lemma modelCategory_hasFunctorialFactorization_cofibration_trivialFibration :
    let := modelCategory R
    (cofibrations (Mon (Complex R))).HasFunctorialFactorization
      (trivialFibrations (Mon (Complex R))) := by
  let := modelCategory R
  have := modelCategory_cofibrantlyGenerated R
  exact _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.hasFunctorialFactorization_cofibration_trivialFibration
    (generatingCofibrations (R := R)) (generatingTrivialCofibrations (R := R))

/-- 概要：同じ実自由生成 trivial cofibration も関手的分解を与える。
方針：同じ生成モデルの第二の関手的分解定理を使う。
規約：実モデルを局所選択する。使われ方：一般の frame 補助比較への代入。 -/
lemma modelCategory_hasFunctorialFactorization_trivialCofibration_fibration :
    let := modelCategory R
    (trivialCofibrations (Mon (Complex R))).HasFunctorialFactorization
      (fibrations (Mon (Complex R))) := by
  let := modelCategory R
  have := modelCategory_cofibrantlyGenerated R
  exact _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.hasFunctorialFactorization_trivialCofibration_fibration
    (generatingCofibrations (R := R)) (generatingTrivialCofibrations (R := R))

/-- 概要：実 dg モデルの第一の関手的分解をデータとして公開する。
方針：証明済みの小対象論法による存在から同じ全射族を選ぶ。
規約：全対象・全射に一つの選択。使われ方：source frame の関手的な構成。 -/
def cofibrantFactorization :
    let := modelCategory R
    MorphismProperty.FunctorialFactorizationData (cofibrations (Mon (Complex R)))
      (trivialFibrations (Mon (Complex R))) := by
  let := modelCategory R
  have := modelCategory_hasFunctorialFactorization_cofibration_trivialFibration R
  exact MorphismProperty.functorialFactorizationData _ _

/-- 概要：実 dg モデルの第二の関手的分解を同じ形で公開する。
方針：証明済みの自由 J の小対象論法から関手的データを選ぶ。
規約：全対象・全射に一つの選択。使われ方：一般の三本矢比較の補助入力。 -/
def fibrantFactorization :
    let := modelCategory R
    MorphismProperty.FunctorialFactorizationData (trivialCofibrations (Mon (Complex R)))
      (fibrations (Mon (Complex R))) := by
  let := modelCategory R
  have := modelCategory_hasFunctorialFactorization_trivialCofibration_fibration R
  exact MorphismProperty.functorialFactorizationData _ _

/-- 概要：実 cofibrant dg 代数の包含は元の全 hammock Hom 射を弱同値にする。
方針：実 I の小対象論法から第一の関手的分解を局所供給する。
規約：係数環以外のモデル・分解仮定を残さない。
使われ方：Sp の全 dg 代数の指定局所化への復帰。 -/
lemma cofibrantHammockInclusion_weak :
    let := modelCategory R
    ∀ X Y : (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.modelCofibrantRelativeCategory (Mon (Complex R))).category,
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence
        (Hammock.Relative.colimitMap (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelCofibrantToModelRelative (Mon (Complex R))) X Y) := by
  let := modelCategory R
  have := modelCategory_hasFunctorialFactorization_cofibration_trivialFibration R
  exact _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelCofibrantToModel_colimitMap_weak (Mon (Complex R))

/-- 概要：実 cofibrant dg 代数の包含は全 hammock coherent nerve の同値。
方針：実 I の小対象論法から一般比較の分解仮定を放電する。
規約：係数環以外の追加仮定なし。使われ方：Sp の全 dg 局所化への復帰。 -/
lemma cofibrantHammockNerveInclusion_isQCatEquivalence :
    let := modelCategory R
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.relativeKanHammockNerve
      (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelCofibrantToModelRelative (Mon (Complex R)))) := by
  let := modelCategory R
  have := modelCategory_hasFunctorialFactorization_cofibration_trivialFibration R
  exact _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.modelCofibrantToModel_nerve_isQCatEquivalence (Mon (Complex R))

end SerrePositivity.EInfinity.DGAlgebra
