module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.DifferentialGraded.Algebras.AWPath
public import SerrePositivity.DifferentialGraded.Algebras.PathAcyclicity

/-!
概要：任意可換環上の dg 代数に実右転送モデル構造を構成する。
方針：自由 I/J の小対象性と実 AW path の acyclicity を右転送へ渡す。
規約：モデル構造は明示的に局所選択し、大域 instance は追加しない。
使われ方：dg 代数の全射擬同型分解と写像空間の frame 比較。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.DGAlgebra
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomologicalComplex _root_.HomotopicalAlgebra
open _root_.SerrePositivity.DifferentialGraded
variable (R : Type u) [CommRing R]

attribute [local instance] _root_.SerrePositivity.DGAlgebra.hasColimits _root_.SerrePositivity.DGAlgebra.hasFiniteLimits _root_.SerrePositivity.DGAlgebra.hasBinaryProducts _root_.SerrePositivity.DGAlgebra.hasTerminal
  _root_.SerrePositivity.DGAlgebra.generatingCofibrations_smallObjectArgument _root_.SerrePositivity.DGAlgebra.generatingTrivialCofibrations_smallObjectArgument

/-- 概要：元の dg モノイド圏の完全な転送モデル構造。
方針：実自由随伴と AW path object を右転送へ代入する。
規約：任意可換環、始域の cofibrancy 仮定なし、大域 instance にしない。
使われ方：全射擬同型の実分解と導来写像空間。 -/
@[instance_reducible]
def modelCategory : ModelCategory (Mon (Complex R)) := by
  let := _root_.SerrePositivity.ProjectiveModel.projectiveModelCategory R
  have := _root_.SerrePositivity.ProjectiveModel.projectiveModelCategory_cofibrantlyGenerated R
  have : ((_root_.SerrePositivity.ProjectiveModel.projectiveGeneratingCofibrations R).strictMap
      (_root_.SerrePositivity.DGAlgebra.freeFunctor (R := R))).HasSmallObjectArgument.{u} :=
    _root_.SerrePositivity.DGAlgebra.generatingCofibrations_smallObjectArgument
  have : ((_root_.SerrePositivity.ProjectiveModel.projectiveGeneratingTrivialCofibrations R).strictMap
      (_root_.SerrePositivity.DGAlgebra.freeFunctor (R := R))).HasSmallObjectArgument.{u} :=
    _root_.SerrePositivity.DGAlgebra.generatingTrivialCofibrations_smallObjectArgument
  exact _root_.SerrePositivity.ModelGeneration.rightTransfer (_root_.SerrePositivity.ProjectiveModel.projectiveGeneratingCofibrations R)
    (_root_.SerrePositivity.ProjectiveModel.projectiveGeneratingTrivialCofibrations R) _root_.SerrePositivity.DGAlgebra.freeForgetAdjunction
    (_root_.SerrePositivity.DGAlgebra.freeCells_acyclic (_root_.SerrePositivity.DGAlgebra.awPathInput R))

/-- 概要：dg 代数の弱同値は元の底の擬同型。
方針：転送のクラスを評価する。規約：モデル構造のフィールドを指定する。
使われ方：擬同型局所化への入力。 -/
lemma modelCategory_weakEquivalences :
    @weakEquivalences (Mon (Complex R)) _ (_root_.SerrePositivity.DGAlgebra.modelCategory R).categoryWithWeakEquivalences =
      (quasiIso (ModuleCat R) (.up ℤ)).inverseImage (Mon.forget (Complex R)) := rfl

/-- 概要：dg 代数の fibration は元の底の次数別全射。
方針：転送の右類を評価する。規約：追加のモデル仮定なし。
使われ方：実 fibration と全射擬同型の判定。 -/
lemma modelCategory_fibrations :
    @fibrations (Mon (Complex R)) _ (_root_.SerrePositivity.DGAlgebra.modelCategory R).categoryWithFibrations =
      (_root_.SerrePositivity.ProjectiveModel.projectiveFibrations R).inverseImage (Mon.forget (Complex R)) := rfl

/-- 概要：指定した実自由 I/J による余生成。
方針：同じ右転送の生成類判定を使う。規約：小対象論法の宇宙は基礎環の u。
使われ方：実 cell 分解と cofibrant 置換。 -/
lemma modelCategory_cofibrantlyGenerated :
    let := _root_.SerrePositivity.DGAlgebra.modelCategory R
    _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{u}
      (_root_.SerrePositivity.DGAlgebra.generatingCofibrations (R := R)) (_root_.SerrePositivity.DGAlgebra.generatingTrivialCofibrations (R := R)) := by
  let := _root_.SerrePositivity.ProjectiveModel.projectiveModelCategory R
  have := _root_.SerrePositivity.ProjectiveModel.projectiveModelCategory_cofibrantlyGenerated R
  have : ((_root_.SerrePositivity.ProjectiveModel.projectiveGeneratingCofibrations R).strictMap
      (_root_.SerrePositivity.DGAlgebra.freeFunctor (R := R))).HasSmallObjectArgument.{u} :=
    _root_.SerrePositivity.DGAlgebra.generatingCofibrations_smallObjectArgument
  have : ((_root_.SerrePositivity.ProjectiveModel.projectiveGeneratingTrivialCofibrations R).strictMap
      (_root_.SerrePositivity.DGAlgebra.freeFunctor (R := R))).HasSmallObjectArgument.{u} :=
    _root_.SerrePositivity.DGAlgebra.generatingTrivialCofibrations_smallObjectArgument
  exact _root_.SerrePositivity.ModelGeneration.rightTransfer_cofibrantlyGenerated
    (_root_.SerrePositivity.ProjectiveModel.projectiveGeneratingCofibrations R) (_root_.SerrePositivity.ProjectiveModel.projectiveGeneratingTrivialCofibrations R)
    _root_.SerrePositivity.DGAlgebra.freeForgetAdjunction (_root_.SerrePositivity.DGAlgebra.freeCells_acyclic (_root_.SerrePositivity.DGAlgebra.awPathInput R))

/-- 概要：元の dg 代数の忘却は右 Quillen。
方針：二つの右類が底で作られることを使う。
規約：両モデル構造を局所的に選ぶ。使われ方：導来忘却と frame の比較。 -/
lemma forget_isRightQuillen :
    let := _root_.SerrePositivity.ProjectiveModel.projectiveModelCategory R
    let := _root_.SerrePositivity.DGAlgebra.modelCategory R
    SerrePositivity.Quillen.IsRightQuillen (Mon.forget (Complex R)) := by
  let := _root_.SerrePositivity.ProjectiveModel.projectiveModelCategory R
  have := _root_.SerrePositivity.ProjectiveModel.projectiveModelCategory_cofibrantlyGenerated R
  have : ((_root_.SerrePositivity.ProjectiveModel.projectiveGeneratingCofibrations R).strictMap
      (_root_.SerrePositivity.DGAlgebra.freeFunctor (R := R))).HasSmallObjectArgument.{u} :=
    _root_.SerrePositivity.DGAlgebra.generatingCofibrations_smallObjectArgument
  have : ((_root_.SerrePositivity.ProjectiveModel.projectiveGeneratingTrivialCofibrations R).strictMap
      (_root_.SerrePositivity.DGAlgebra.freeFunctor (R := R))).HasSmallObjectArgument.{u} :=
    _root_.SerrePositivity.DGAlgebra.generatingTrivialCofibrations_smallObjectArgument
  exact _root_.SerrePositivity.ModelGeneration.rightTransfer_isRightQuillen (_root_.SerrePositivity.ProjectiveModel.projectiveGeneratingCofibrations R)
    (_root_.SerrePositivity.ProjectiveModel.projectiveGeneratingTrivialCofibrations R) _root_.SerrePositivity.DGAlgebra.freeForgetAdjunction
    (_root_.SerrePositivity.DGAlgebra.freeCells_acyclic (_root_.SerrePositivity.DGAlgebra.awPathInput R))

/-- 概要：この転送モデルでは全 dg 代数が fibrant。
方針：終対象への底の射が全次数全射であることを使う。
規約：同じ実モデル構造を局所選択する。使われ方：frame Hom の終域条件。 -/
lemma allFibrant (B : Mon (Complex R)) :
    let := _root_.SerrePositivity.DGAlgebra.modelCategory R
    IsFibrant B := by
  let := _root_.SerrePositivity.DGAlgebra.modelCategory R
  exact ⟨_root_.SerrePositivity.DGAlgebra.terminalFrom_projectiveFibration R B⟩

end SerrePositivity.DGAlgebra

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HA "4.1.8.3" (partial := special) "仮定：可換環 R 上の鎖複体に射影モデル構造を選ぶ（Lean は底をこの例に固定）。結論：厳密な結合 dg 代数にモデル構造があり、弱同値は底の擬同型、ファイブレーションは底の射影ファイブレーション、忘却は右 Quillen（(1) のモデル構造と右類の記述および (2) に一致）。組合せ性・単体モデル構造・左固有性はこの型に含まれない。"] _root_.SerrePositivity.DGAlgebra.forget_isRightQuillen
attribute [cite HA "4.1.8.3" (partial := special) "仮定：可換環 R 上の鎖複体に射影モデル構造を選ぶ（Lean は底をこの例に固定）。結論：厳密な結合 dg 代数にモデル構造があり、弱同値は底の擬同型、ファイブレーションは底の射影ファイブレーション、忘却は右 Quillen（(1) のモデル構造と右類の記述および (2) に一致）。組合せ性・単体モデル構造・左固有性はこの型に含まれない。"] _root_.SerrePositivity.DGAlgebra.modelCategory
attribute [cite HA "4.1.8.3" (partial := special) "仮定：可換環 R 上の鎖複体に射影モデル構造を選ぶ（Lean は底をこの例に固定）。結論：厳密な結合 dg 代数にモデル構造があり、弱同値は底の擬同型、ファイブレーションは底の射影ファイブレーション、忘却は右 Quillen（(1) のモデル構造と右類の記述および (2) に一致）。組合せ性・単体モデル構造・左固有性はこの型に含まれない。"] _root_.SerrePositivity.DGAlgebra.modelCategory_fibrations
attribute [cite HA "4.1.8.3" (partial := special) "仮定：可換環 R 上の鎖複体に射影モデル構造を選ぶ（Lean は底をこの例に固定）。結論：厳密な結合 dg 代数にモデル構造があり、弱同値は底の擬同型、ファイブレーションは底の射影ファイブレーション、忘却は右 Quillen（(1) のモデル構造と右類の記述および (2) に一致）。組合せ性・単体モデル構造・左固有性はこの型に含まれない。"] _root_.SerrePositivity.DGAlgebra.modelCategory_weakEquivalences
attribute [cite HA "7.1.4.5" (partial := component) "仮定：任意可換環 R と厳密 dg 代数 Mon(Complex R)（HA と一致する模型）。結論：実モデル構造を構成し、弱同値を底の擬同型、fibration を底の次数別全射と同定する（モデル構造・W・F の部分に一致）。combinatorial 性と体上の左固有性は含まれない。ModelCategory は構成済み。"] _root_.SerrePositivity.DGAlgebra.modelCategory
attribute [cite HA "7.1.4.5" (partial := component) "仮定：任意可換環 R と厳密 dg 代数 Mon(Complex R)（HA と一致する模型）。結論：実モデル構造を構成し、弱同値を底の擬同型、fibration を底の次数別全射と同定する（モデル構造・W・F の部分に一致）。combinatorial 性と体上の左固有性は含まれない。ModelCategory は構成済み。"] _root_.SerrePositivity.DGAlgebra.modelCategory_fibrations
attribute [cite HA "7.1.4.5" (partial := component) "仮定：任意可換環 R と厳密 dg 代数 Mon(Complex R)（HA と一致する模型）。結論：実モデル構造を構成し、弱同値を底の擬同型、fibration を底の次数別全射と同定する（モデル構造・W・F の部分に一致）。combinatorial 性と体上の左固有性は含まれない。ModelCategory は構成済み。"] _root_.SerrePositivity.DGAlgebra.modelCategory_weakEquivalences
