module

public import SerrePositivity.EInfinity.DGAlgebra.AWPath
public import SerrePositivity.EInfinity.DGAlgebra.PathAcyclicity

/-!
概要：任意可換環上の dg 代数に実右転送モデル構造を構成する。
方針：自由 I/J の小対象性と実 AW path の acyclicity を右転送へ渡す。
規約：モデル構造は明示的に局所選択し、大域 instance は追加しない。
使われ方：dg 代数の全射擬同型分解と写像空間の frame 比較。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.EInfinity.DGAlgebra
open CategoryTheory Limits HomologicalComplex HomotopicalAlgebra
open SerrePositivity.DifferentialGraded
variable (R : Type u) [CommRing R]

attribute [local instance] hasColimits hasFiniteLimits hasBinaryProducts hasTerminal
  generatingCofibrations_smallObjectArgument generatingTrivialCofibrations_smallObjectArgument

/-- 概要：元の dg モノイド圏の完全な転送モデル構造。
方針：実自由随伴と AW path object を右転送へ代入する。
規約：任意可換環、始域の cofibrancy 仮定なし、大域 instance にしない。
使われ方：全射擬同型の実分解と導来写像空間。 -/
@[instance_reducible]
def modelCategory : ModelCategory (Mon (Complex R)) := by
  let := projectiveModelCategory R
  have := projectiveModelCategory_cofibrantlyGenerated R
  have : ((projectiveGeneratingCofibrations R).strictMap
      (freeFunctor (R := R))).HasSmallObjectArgument.{u} :=
    generatingCofibrations_smallObjectArgument
  have : ((projectiveGeneratingTrivialCofibrations R).strictMap
      (freeFunctor (R := R))).HasSmallObjectArgument.{u} :=
    generatingTrivialCofibrations_smallObjectArgument
  exact ModelGeneration.rightTransfer (projectiveGeneratingCofibrations R)
    (projectiveGeneratingTrivialCofibrations R) freeForgetAdjunction
    (freeCells_acyclic (awPathInput R))

/-- 概要：dg 代数の弱同値は元の底の擬同型。
方針：転送のクラスを評価する。規約：モデル構造のフィールドを指定する。
使われ方：擬同型局所化への入力。 -/
lemma modelCategory_weakEquivalences :
    @weakEquivalences (Mon (Complex R)) _ (modelCategory R).categoryWithWeakEquivalences =
      (quasiIso (ModuleCat R) (.up ℤ)).inverseImage (Mon.forget (Complex R)) := rfl

/-- 概要：dg 代数の fibration は元の底の次数別全射。
方針：転送の右類を評価する。規約：追加のモデル仮定なし。
使われ方：実 fibration と全射擬同型の判定。 -/
lemma modelCategory_fibrations :
    @fibrations (Mon (Complex R)) _ (modelCategory R).categoryWithFibrations =
      (projectiveFibrations R).inverseImage (Mon.forget (Complex R)) := rfl

/-- 概要：指定した実自由 I/J による余生成。
方針：同じ右転送の生成類判定を使う。規約：小対象論法の宇宙は基礎環の u。
使われ方：実 cell 分解と cofibrant 置換。 -/
lemma modelCategory_cofibrantlyGenerated :
    let := modelCategory R
    _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{u}
      (generatingCofibrations (R := R)) (generatingTrivialCofibrations (R := R)) := by
  let := projectiveModelCategory R
  have := projectiveModelCategory_cofibrantlyGenerated R
  have : ((projectiveGeneratingCofibrations R).strictMap
      (freeFunctor (R := R))).HasSmallObjectArgument.{u} :=
    generatingCofibrations_smallObjectArgument
  have : ((projectiveGeneratingTrivialCofibrations R).strictMap
      (freeFunctor (R := R))).HasSmallObjectArgument.{u} :=
    generatingTrivialCofibrations_smallObjectArgument
  exact ModelGeneration.rightTransfer_cofibrantlyGenerated
    (projectiveGeneratingCofibrations R) (projectiveGeneratingTrivialCofibrations R)
    freeForgetAdjunction (freeCells_acyclic (awPathInput R))

/-- 概要：元の dg 代数の忘却は右 Quillen。
方針：二つの右類が底で作られることを使う。
規約：両モデル構造を局所的に選ぶ。使われ方：導来忘却と frame の比較。 -/
lemma forget_isRightQuillen :
    let := projectiveModelCategory R
    let := modelCategory R
    SerrePositivity.Quillen.IsRightQuillen (Mon.forget (Complex R)) := by
  let := projectiveModelCategory R
  have := projectiveModelCategory_cofibrantlyGenerated R
  have : ((projectiveGeneratingCofibrations R).strictMap
      (freeFunctor (R := R))).HasSmallObjectArgument.{u} :=
    generatingCofibrations_smallObjectArgument
  have : ((projectiveGeneratingTrivialCofibrations R).strictMap
      (freeFunctor (R := R))).HasSmallObjectArgument.{u} :=
    generatingTrivialCofibrations_smallObjectArgument
  exact ModelGeneration.rightTransfer_isRightQuillen (projectiveGeneratingCofibrations R)
    (projectiveGeneratingTrivialCofibrations R) freeForgetAdjunction
    (freeCells_acyclic (awPathInput R))

/-- 概要：この転送モデルでは全 dg 代数が fibrant。
方針：終対象への底の射が全次数全射であることを使う。
規約：同じ実モデル構造を局所選択する。使われ方：frame Hom の終域条件。 -/
lemma allFibrant (B : Mon (Complex R)) :
    let := modelCategory R
    IsFibrant B := by
  let := modelCategory R
  exact ⟨terminalFrom_projectiveFibration R B⟩

end SerrePositivity.EInfinity.DGAlgebra
