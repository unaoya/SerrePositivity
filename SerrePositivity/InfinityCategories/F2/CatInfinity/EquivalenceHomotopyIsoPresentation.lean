module

public import SerrePositivity.InfinityCategories.Core.EquivalencePathIso

/-!
概要：可逆ホモトピーから作る指定同型の fiber による表示。
方針：構成中の可逆 path への lift と比較同型を取り出す。
規約：指定された三角形と同型の値を保持する。
使われ方：引き戻し錐と指定 path の比較を簡約する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

variable {A Y : SSet.{u}}
variable (H : (Δ[1] : SSet.{u}) ⊗ A ⟶ Y)
variable (hH : ∀ x : A _⦋0⦌, IsInvertibleEdge (edgeOfSimplex
      (H.app (Opposite.op ⦋1⦌)
        (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})), PinchedHom.constant x 1))))
/-- 概要：可逆ホモトピーの指定同型の構成元を明示する。
方針：可逆 path への lift と端点評価を使う。
規約：元の同型を新しく選ばず型の輸送だけを除く。
使われ方：定値 path の切断上の指定同型の簡約。 -/
def equivalenceHomotopyPathLift : A ⟶ equivalencePath Y :=
  fullSubcomplexLift IsEquivalencePathVertex (curry H) (fun x ↦ by
    unfold IsEquivalencePathVertex
    rw [intervalFunctorVertexEdge_curry]
    exact hH x)
/-- 概要：可逆ホモトピーの指定同型の構成元を明示する。
方針：可逆 path への lift と端点評価を使う。
規約：元の同型を新しく選ばず型の輸送だけを除く。
使われ方：定値 path の切断上の指定同型の簡約。 -/
lemma equivalenceHomotopyPathLift_ι :
    equivalenceHomotopyPathLift H hH ≫ equivalencePathι Y = curry H :=
  fullSubcomplexLift_ι _ _ _
/-- 概要：可逆ホモトピーの指定同型の構成元を明示する。
方針：可逆 path への lift と端点評価を使う。
規約：元の同型を新しく選ばず型の輸送だけを除く。
使われ方：定値 path の切断上の指定同型の簡約。 -/
lemma equivalenceHomotopyPathLift_endpoint (i : Fin 2) :
    equivalenceHomotopyPathLift H hH ≫ equivalencePathEndpoint Y i = prismEndpoint i A ≫ H := by
  change equivalenceHomotopyPathLift H hH ≫ equivalencePathι Y ≫ evaluateFunctorAt _ = _
  rw [← Category.assoc, equivalenceHomotopyPathLift_ι, curry_evaluateFunctorAt_interval]
variable [Quasicategory Y]

/-- 概要：可逆ホモトピーの指定同型の構成元を明示する。
方針：可逆 path への lift と端点評価を使う。
規約：元の同型を新しく選ばず型の輸送だけを除く。
使われ方：定値 path の切断上の指定同型の簡約。 -/
def equivalenceHomotopyFiberIso :
    FunctorIso (equivalenceHomotopyPathLift H hH)
      ((prismEndpoint 0 A ≫ H) ≫ equivalencePathRefl Y) :=
  functorIsoOfTrivialKanFibration (equivalencePathEndpoint Y 0)
    (equivalenceHomotopyPathLift H hH) ((prismEndpoint 0 A ≫ H) ≫ equivalencePathRefl Y)
    (by rw [equivalenceHomotopyPathLift_endpoint, Category.assoc,
      equivalencePathRefl_endpoint, Category.comp_id])
/-- 概要：可逆ホモトピーの指定同型の構成元を明示する。
方針：可逆 path への lift と端点評価を使う。
規約：元の同型を新しく選ばず型の輸送だけを除く。
使われ方：定値 path の切断上の指定同型の簡約。 -/
lemma functorIsoOfEquivalenceHomotopy_heq :
    HEq (functorIsoOfEquivalenceHomotopy H hH)
      (FunctorIso.postcomp (equivalenceHomotopyFiberIso H hH).symm
        (equivalencePathEndpoint Y 1)) := by
  unfold functorIsoOfEquivalenceHomotopy
  exact (cast_heq _ _).trans ((cast_heq _ _).trans (HEq.refl _))

end SerrePositivity.InfinityCategories.F2
