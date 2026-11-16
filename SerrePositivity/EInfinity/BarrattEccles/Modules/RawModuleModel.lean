module

public import SerrePositivity.EInfinity.BarrattEccles.Modules.RawModuleAcyclicity
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal

/-!
# 固定 BE 底上の通常 dg 加群の実 projective モデル構造

概要：N01 の同じ通常加群圏に右転送を実際に構成する。
方針：既存の複体モデル・自由評価随伴と証明済み小対象性・非輪状性を使う。
規約：ModelCategory を入力とせず、大域 instance を追加しない。
使われ方：元の相対圏の frame と dg nerve の比較。
文献：Keller, On differential graded categories, Theorem 3.2 (1)
https://webusers.imj-prg.fr/~bernhard.keller/publ/dgcat.pdf 。
HA Proposition 4.3.3.15 の一般の代数 cofibrancy 仮定は使わない。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory Limits HomologicalComplex HomotopicalAlgebra
open SerrePositivity.DifferentialGraded
open SerrePositivity.InfinityCategories.HA.Section7_1_1
variable (A : Type u) [CommRing A]

/-- 概要：元の加群圏の実有限極限。
方針：既存の評価ごとの極限を使う。
規約：モデル構造の仮定なし。使われ方：右転送の CM1。
文献：Keller, Theorem 3.2 (1) の構成の成分。 -/
lemma strictRawModule_hasFiniteLimits (X : (operad A).Algebra) :
    HasFiniteLimits (strictRawModuleCategory A X) where
  out J _ _ := by infer_instance

/-- 概要：元の加群圏の実有限余極限。
方針：既存の評価ごとの余極限を使う。
規約：モデル構造の仮定なし。使われ方：右転送の CM1。
文献：Keller, Theorem 3.2 (1) の構成の成分。 -/
lemma strictRawModule_hasFiniteColimits (X : (operad A).Algebra) :
    HasFiniteColimits (strictRawModuleCategory A X) where
  out J _ _ := by infer_instance

attribute [local instance] strictRawModule_hasFiniteLimits strictRawModule_hasFiniteColimits
  strictRawModuleGeneratingCofibrations_smallObjectArgument
  strictRawModuleGeneratingTrivialCofibrations_smallObjectArgument

/-- 概要：同じ BE 固定底上の通常 dg 加群の実 projective モデル構造。
方針：実自由随伴・小対象性・disk 被覆による非輪状性を一般右転送に渡す。
規約：Keller Theorem 3.2 (1)、任意可換環・任意の厳密 BE 底。
使われ方：元の通常相対圏の実モデル入力。 -/
@[instance_reducible]
def strictRawModuleModelCategory (X : (operad A).Algebra) :
    ModelCategory (strictRawModuleCategory A X) := by
  let := projectiveModelCategory A
  have := projectiveModelCategory_cofibrantlyGenerated A
  have : ((projectiveGeneratingCofibrations A).strictMap (strictRawModuleFree A X)).HasSmallObjectArgument.{u} :=
    strictRawModuleGeneratingCofibrations_smallObjectArgument A X
  have : ((projectiveGeneratingTrivialCofibrations A).strictMap (strictRawModuleFree A X)).HasSmallObjectArgument.{u} :=
    strictRawModuleGeneratingTrivialCofibrations_smallObjectArgument A X
  exact ModelGeneration.rightTransfer (projectiveGeneratingCofibrations A)
    (projectiveGeneratingTrivialCofibrations A) (strictRawModuleFreeAdjunction A X) (by
      change _ ≤ (quasiIso (ModuleCat A) (.up ℤ)).inverseImage (strictRawModuleUnderlying X)
      rw [← strictRawModuleQuasiIso_eq A X]
      exact strictRawModuleFreeCells_acyclic A X)

/-- 概要：実モデルの弱同値は同じ元の objectwise 擬同型。
方針：転送の右類を唯一点の擬同型検出と照合する。
規約：同じ実モデル。使われ方：元の相対局所化への入力。
文献：Keller, Theorem 3.2 (1) の構成の成分。 -/
lemma strictRawModuleModelCategory_weakEquivalences (X : (operad A).Algebra) :
    @weakEquivalences (strictRawModuleCategory A X) _
      (strictRawModuleModelCategory A X).categoryWithWeakEquivalences =
        moduleQuasiIso A (dgAlgebraCategory A ((assocForget A).obj X)) := by
  exact (strictRawModuleQuasiIso_eq A X).symm

/-- 概要：実モデルの fibration は同じ台の次数別全射。
方針：右転送の定義を評価する。
規約：全整数次数。使われ方：元の全射擬同型の持ち上げ。
文献：Keller, Theorem 3.2 (1) の構成の成分。 -/
lemma strictRawModuleModelCategory_fibrations (X : (operad A).Algebra) :
    @fibrations (strictRawModuleCategory A X) _
      (strictRawModuleModelCategory A X).categoryWithFibrations =
        (projectiveFibrations A).inverseImage (strictRawModuleUnderlying X) := rfl

/-- 概要：実自由 I/J は同じ構成済みモデルを生成する。
方針：一般右転送の生成類の法則を使う。
規約：基礎環と同じ小対象宇宙 u。使われ方：実関手的分解と frame。
文献：Keller, Theorem 3.2 (1) の構成の成分。 -/
lemma strictRawModuleModelCategory_cofibrantlyGenerated (X : (operad A).Algebra) :
    let := strictRawModuleModelCategory A X
    SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{u}
      (strictRawModuleGeneratingCofibrations A X)
      (strictRawModuleGeneratingTrivialCofibrations A X) := by
  let := projectiveModelCategory A
  have := projectiveModelCategory_cofibrantlyGenerated A
  have : ((projectiveGeneratingCofibrations A).strictMap (strictRawModuleFree A X)).HasSmallObjectArgument.{u} :=
    strictRawModuleGeneratingCofibrations_smallObjectArgument A X
  have : ((projectiveGeneratingTrivialCofibrations A).strictMap (strictRawModuleFree A X)).HasSmallObjectArgument.{u} :=
    strictRawModuleGeneratingTrivialCofibrations_smallObjectArgument A X
  exact ModelGeneration.rightTransfer_cofibrantlyGenerated (projectiveGeneratingCofibrations A)
    (projectiveGeneratingTrivialCofibrations A) (strictRawModuleFreeAdjunction A X) (by
      change _ ≤ (quasiIso (ModuleCat A) (.up ℤ)).inverseImage (strictRawModuleUnderlying X)
      rw [← strictRawModuleQuasiIso_eq A X]
      exact strictRawModuleFreeCells_acyclic A X)

/-- 概要：全ての元の通常 dg 加群は構成済みモデルで fibrant。
方針：台と各次数の評価が終対象を保つので終域が零加群となる。
規約：モデル構造は実構成を局所選択。使われ方：同じ対象の right frame。
文献：Keller, Theorem 3.2 (1) の構成の成分。 -/
lemma strictRawModuleModelCategory_allFibrant (X : (operad A).Algebra)
    (M : strictRawModuleCategory A X) :
    let := strictRawModuleModelCategory A X
    IsFibrant M := by
  let := strictRawModuleModelCategory A X
  apply (isFibrant_iff_of_isTerminal (terminal.from M) terminalIsTerminal).mpr
  apply (fibration_iff _).mpr
  intro n y
  let F := strictRawModuleUnderlying X ⋙ eval (ModuleCat.{u} A) (.up ℤ) n
  have ht : IsTerminal (F.obj (⊤_ (strictRawModuleCategory A X))) :=
    terminalIsTerminal.isTerminalObj
      (moduleEvaluation A (dgAlgebraCategory A ((assocForget A).obj X))
        (Opposite.op DGAlgebraPoint.star) ⋙ eval (ModuleCat.{u} A) (.up ℤ) n)
  have hz : IsZero (F.obj (⊤_ (strictRawModuleCategory A X))) :=
    (isZero_zero (ModuleCat.{u} A)).of_iso
      (ht.uniqueUpToIso (isZero_zero (ModuleCat.{u} A)).isTerminal)
  have hs : Subsingleton (F.obj (⊤_ (strictRawModuleCategory A X))) :=
    ModuleCat.subsingleton_of_isZero hz
  exact ⟨0, hs.elim _ _⟩

end SerrePositivity.EInfinity.BarrattEccles
