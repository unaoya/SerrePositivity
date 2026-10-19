module

public import SerrePositivity.KST.DerivedBlowup.FiniteOverlapExceptionalAlgebraVertexComparison
public import SerrePositivity.KST.DerivedBlowup.FiniteOverlapExceptionalModuleComparison

/-!
概要：KST v4 §3.1・Lemma 3.6（pp.11–14）の一対象正規表示と 例外因子 Koszul 模型の局所遷移の比較。
方針：両表示の遷移を共通の自己 Hom の射として比較する。
規約：全図式の係数圏を保持し、局所表示の変更だけを扱う。
使われ方：canonical な cartesian 比較の二つの表示の同定。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory
open DifferentialGraded

variable (R : Type u) [CommRing R] {I : Type} [DecidableEq I]

set_option maxHeartbeats 2000000 in
-- 二つの局所化環の基底制限後の Hom を照合するために必要。
set_option synthInstance.maxHeartbeats 100000 in
-- 局所化環からの基底制限の dg 構造を照合するために必要。
/-- 概要：正規表示と元の Koszul 模型の指定 dg 比較は局所遷移と整合する。
方針：対象は標準点で一致し、Hom は同じ指定 dg 代数射である。
規約：KST v4 §3.1・Lemma 3.6（pp.11–14）。使われ方：局所制限の表示比較の可換四角形。 -/
theorem finiteOverlapExceptionalAlgebraVertexToChart_transition (a : I → R)
    {T U : FiniteOverlapIndex I} (h : T ≤ U) :
    (finiteOverlapExceptionalAlgebraVertexToChart R a T).comp
      (finiteOverlapExceptionalLocalDGTransition R a h) =
      (diagramAlgebraVertexTransition (finiteOverlapExceptionalDGAlgebraDiagram R a) h).comp
        (finiteOverlapExceptionalAlgebraVertexToChart R a U) := by
  refine EnrichedFunctor.ext (Complex R) (fun _ => rfl) ?_
  intro x y
  cases x
  cases y
  simp only [eqToHom_refl, Category.comp_id]
  change 𝟙 _ ≫ (finiteOverlapExceptionalLocalDGTransition R a h).map .point .point =
    (finiteOverlapExceptionalLocalDGTransition R a h).map .point .point ≫ 𝟙 _
  simp only [Category.id_comp, Category.comp_id]

end SerrePositivity.KST.DerivedBlowup
