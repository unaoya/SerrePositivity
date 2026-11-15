module
public import SerrePositivity.EInfinity.Modules.SimplexEquationEvaluation

/-!
概要：元の加群対象が一致する dg 単体を、全対象での評価により比較する。
方針：対象族の等式を先に消去し、Hom end の外延性を各斉次成分に適用する。
規約：HA Construction 1.3.1.6、全有限部分集合・全整数次数。
使われ方：M10 の同じ三相データの全評価と面・退化の比較。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.EInfinity.Modules
open CategoryTheory
open SerrePositivity.DifferentialGraded
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 概要：同じ加群対象族上の全データの等式を各対象での評価から戻す。
方針：対象の同一視の後、全斉次係数について Hom end の外延性を使う。
規約：HA 1.3.1.6、対象の等式も入力する。使われ方：全三角形の貼り合わせ。 -/
lemma moduleSimplexData_ext_of_evaluation {n : ℕ}
    (s t : SimplexData A (RightModule A D) n) (ho : s.obj = t.obj)
    (h : ∀ x : D, s.map (moduleEvaluationDG A D x) =
      t.map (moduleEvaluationDG A D x)) : s = t := by
  rcases s with ⟨os, fs⟩
  rcases t with ⟨ot, ft⟩
  dsimp only at ho
  cases ho
  apply SimplexData.ext (s := ⟨os, fs⟩) (t := ⟨os, ft⟩) rfl
  apply heq_of_eq
  funext I a b k hI ha hb hk
  apply moduleHomElement_ext A D
  intro x
  have he := congrArg (fun z : SimplexData A (Complex A) n =>
    (⟨z.obj, z.hom⟩ : Σ o, HomFamily A (Complex A) o)) (h x)
  have hh := (Sigma.mk.inj he).2
  exact congrArg (fun f : HomFamily A (Complex A)
    (fun i => (moduleEvaluationDG A D x).obj (os i)) =>
      f I a b k hI ha hb hk) (eq_of_heq hh)

/-- 概要：同じ加群頂点族上の実 dg 単体の等式を全評価から戻す。
方針：全データの等式を戻し、方程式の証明の一意性を使う。
規約：HA 1.3.1.6、全単体。使われ方：面・退化と大域三角形の比較。 -/
lemma moduleSimplex_ext_of_evaluation {n : ℕ}
    (s t : Simplex A (RightModule A D) n) (ho : s.obj = t.obj)
    (h : ∀ x : D, s.toSimplexData.map (moduleEvaluationDG A D x) =
      t.toSimplexData.map (moduleEvaluationDG A D x)) : s = t :=
  Simplex.ext (moduleSimplexData_ext_of_evaluation A D _ _ ho h)

end SerrePositivity.EInfinity.Modules
