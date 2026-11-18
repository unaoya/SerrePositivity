module

public import SerrePositivity.EInfinity.BarrattEccles.ModelCategory
public import Mathlib.AlgebraicTopology.ModelCategory.IsCofibrant

/-!
# E 代数の fibration 判定と全対象の fibrancy

概要：Berger–Moerdijk 命題 4.1 の具体的な転送後、全 E 代数が fibrant である。
方針：fibration は底の全次数全射であり、零代数への射は常に全射となる。
規約：任意の可換環、モデル構造は局所的に選ぶ。
使われ方：E2a-4 の homotopy 引き戻しと E2a-5 の写像空間。
-/

@[expose] public section

noncomputable section

universe u

namespace SerrePositivity.EInfinity.BarrattEccles

open CategoryTheory Limits HomotopicalAlgebra
open scoped ZeroObject
open SerrePositivity.DifferentialGraded

variable (A : Type u) [CommRing A]

/-- 概要：E 代数の fibration は全整数次数での全射（BM 命題 4.1）。
方針：具体的な転送モデル構造の fibration 類を展開する。
規約：モデル構造を局所的に選び、入力仮定にしない。
使われ方：具体的な代数射の fibration 判定。 -/
lemma fibration_iff {X Y : (operad A).Algebra} (f : X ⟶ Y) :
    let := modelCategory A
    Fibration f ↔ ∀ n : ℤ, Function.Surjective (f.hom.f n) := by
  let := modelCategory A
  change Fibration f ↔ _
  rw [HomotopicalAlgebra.fibration_iff, modelCategory_fibrations]
  rfl

/-- 概要：E 代数の弱同値は底の擬同型（BM 命題 4.1）。
方針：具体的な転送モデル構造の弱同値類を展開する。
規約：任意の可換環、局所的なモデル構造。
使われ方：忘却前後の弱同値を同定する。 -/
lemma weakEquivalence_iff {X Y : (operad A).Algebra} (f : X ⟶ Y) :
    let := modelCategory A
    WeakEquivalence f ↔ QuasiIso f.hom := by
  let := modelCategory A
  change WeakEquivalence f ↔ _
  rw [HomotopicalAlgebra.weakEquivalence_iff, modelCategory_weakEquivalences]
  rfl

/-- 概要：具体的なモデル構造ですべての E 代数が fibrant（BM 命題 4.1）。
方針：終対象として零代数を選び、零加群への各次数の射の全射性を示す。
規約：モデル構造も fibrancy も入力仮定にしない。大域 instance は登録しない。
使われ方：E2a-4 の homotopy 引き戻しと E2a-5 の fibrant 置換の省略。 -/
lemma isFibrant (X : (operad A).Algebra) :
    let := modelCategory A
    IsFibrant X := by
  let := modelCategory A
  change IsFibrant X
  apply (isFibrant_iff_of_isTerminal (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.toTerminal (operad A) X)
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.terminalAlgebraIsTerminal (operad A))).mpr
  apply (fibration_iff A _).mpr
  change ∀ n : ℤ, Function.Surjective ((0 : X.carrier ⟶ (0 : Complex A)).f n)
  intro n y
  have hz : IsZero ((0 : Complex A).X n) :=
    (HomologicalComplex.eval (ModuleCat A) (.up ℤ) n).map_isZero (isZero_zero (Complex A))
  have := ModuleCat.subsingleton_of_isZero hz
  exact ⟨0, Subsingleton.elim _ _⟩

end SerrePositivity.EInfinity.BarrattEccles
