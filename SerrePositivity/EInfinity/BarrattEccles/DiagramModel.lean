module
public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.EvaluationFamily

public import SerrePositivity.EInfinity.BarrattEccles.DiagramAcyclicity
public import SerrePositivity.EInfinity.BarrattEccles.Fibrancy

/-!
# 任意の小圏上の E 代数図式の具体的な射影モデル

概要：BM 命題 4.1 の具体的な E 代数モデルを小図式へ拡張する。
方針：評価の随伴族、自由生成射の小対象性、J-cell 非循環性を転送に渡す。
規約：モデル構造は局所的に選び、モデルの存在や局所表示可能性を仮定しない。
使われ方：E2a-4 の一般図式の導来比較、E2a-5 の図式の写像空間。
-/

@[expose] public section

noncomputable section

universe u

namespace SerrePositivity.EInfinity.BarrattEccles.Diagram

open CategoryTheory Limits HomotopicalAlgebra
open _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.AlgebraDiagram

variable (A : Type u) [CommRing A] (K : Type u) [SmallCategory K]

/-- 概要：小さい E 代数図式の完全な射影モデル構造（BM 命題 4.1、Hovey §2.1）。
方針：評価の自由随伴族から二つの小対象分解を構成する。
規約：右類は頂点ごと、cofibration は自由生成類の左持ち上げ性。
使われ方：任意の小図式上の導来忘却の入力モデル。 -/
@[instance_reducible]
def projectiveModelCategory : ModelCategory (K ⥤ (operad A).Algebra) := by
  let := BarrattEccles.modelCategory A
  have := modelCategory_cofibrantlyGenerated A
  exact _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.modelCategory
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.AlgebraDiagram.free (operad A) K) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.AlgebraDiagram.evaluation (operad A) K) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.AlgebraDiagram.adjunction (operad A) K)
    ((_root_.SerrePositivity.ProjectiveModel.projectiveGeneratingCofibrations A).strictMap (operad A).freeAlgebraFunctor)
    ((_root_.SerrePositivity.ProjectiveModel.projectiveGeneratingTrivialCofibrations A).strictMap (operad A).freeAlgebraFunctor)
    (freeCells_acyclic A K)

/-- 概要：小図式の弱同値は各頂点の底の擬同型（BM 命題 4.1）。
方針：評価で検出する弱同値の定義を展開する。
規約：具体的な図式モデルを局所的に選ぶ。
使われ方：元の図式射の弱同値の直接判定。 -/
lemma weakEquivalence_iff {F G : K ⥤ (operad A).Algebra} (f : F ⟶ G) :
    let := projectiveModelCategory A K
    WeakEquivalence f ↔ ∀ k, QuasiIso (f.app k).hom := by
  let := projectiveModelCategory A K
  change WeakEquivalence f ↔ _
  rw [HomotopicalAlgebra.weakEquivalence_iff]
  rfl

/-- 概要：小図式の fibration は各頂点で全整数次数全射（BM 命題 4.1）。
方針：評価の二つの右類の検出を使う。
規約：図式の射を同じ底の複体射で判定する。
使われ方：図式の fibrant 置換と比較。 -/
lemma fibration_iff {F G : K ⥤ (operad A).Algebra} (f : F ⟶ G) :
    let := projectiveModelCategory A K
    Fibration f ↔ ∀ k, ∀ n : ℤ, Function.Surjective ((f.app k).hom.f n) := by
  let := projectiveModelCategory A K
  change Fibration f ↔ _
  rw [HomotopicalAlgebra.fibration_iff]
  rfl

/-- 概要：具体的な図式モデルは指定した自由像で生成される（BM 命題 4.1）。
方針：評価族の転送の生成類判定に証明済み非循環性を渡す。
規約：小対象引数の宇宙は基礎環と同じ u。
使われ方：図式の関手的置換と frame の構成。 -/
lemma cofibrantlyGenerated :
    let := projectiveModelCategory A K
    _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{u}
      (generatingCofibrations A K) (generatingTrivialCofibrations A K) := by
  let := BarrattEccles.modelCategory A
  have := modelCategory_cofibrantlyGenerated A
  exact _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.modelCategory_generated
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.AlgebraDiagram.free (operad A) K) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.AlgebraDiagram.evaluation (operad A) K) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.AlgebraDiagram.adjunction (operad A) K)
    ((_root_.SerrePositivity.ProjectiveModel.projectiveGeneratingCofibrations A).strictMap (operad A).freeAlgebraFunctor)
    ((_root_.SerrePositivity.ProjectiveModel.projectiveGeneratingTrivialCofibrations A).strictMap (operad A).freeAlgebraFunctor)
    (freeCells_acyclic A K)

/-- 概要：すべての小さい E 代数図式は射影モデルで fibrant（BM 命題 4.1）。
方針：評価が終対象を保つことと各 E 代数の fibrancy を使う。
規約：この事実だけでは通常の極限の導来性は主張しない。
使われ方：図式忘却の右導来関手を元の図式で計算する。 -/
lemma isFibrant (F : K ⥤ (operad A).Algebra) :
    let := projectiveModelCategory A K
    IsFibrant F := by
  let := BarrattEccles.modelCategory A
  let := projectiveModelCategory A K
  change IsFibrant F
  apply (isFibrant_iff_of_isTerminal (terminal.from F) terminalIsTerminal).mpr
  apply (HomotopicalAlgebra.fibration_iff _).mpr
  intro k
  have := BarrattEccles.isFibrant A (F.obj k)
  have h := (isFibrant_iff_of_isTerminal ((terminal.from F).app k)
    (terminalIsTerminal.isTerminalObj (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.AlgebraDiagram.evaluation (operad A) K k) _)).mp inferInstance
  exact h.mem

end SerrePositivity.EInfinity.BarrattEccles.Diagram
