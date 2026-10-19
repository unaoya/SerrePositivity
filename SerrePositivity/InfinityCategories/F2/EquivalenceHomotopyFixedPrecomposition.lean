module

public import SerrePositivity.InfinityCategories.F2.EquivalenceHomotopyIsoPresentation
public import SerrePositivity.InfinityCategories.F2.TrivialKanIsoFixedPrecomposition
public import SerrePositivity.InfinityCategories.F2.FunctorEqIsoTransport
public import SerrePositivity.InfinityCategories.F2.FunctorIsoWhiskerComposition

/-!
概要：可逆ホモトピーの lift が定値になる制限での指定同型。
方針：可縮 fiber の指定比較を簡約して端点評価と輸送を戻す。
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

/-- 概要：可逆ホモトピーの lift が定値になる制限での指定同型。
方針：可縮 fiber の指定比較を簡約して端点評価と輸送を戻す。
規約：元の指定同型を保持する。
使われ方：切断上の指定 path の同型の簡約。 -/
lemma equivalenceHomotopyIso_fixed_precomp {A D Y : SSet.{u}} [Quasicategory Y]
    (H : (Δ[1] : SSet.{u}) ⊗ A ⟶ Y)
    (hH : ∀ x : A _⦋0⦌, IsInvertibleEdge (edgeOfSimplex
      (H.app (Opposite.op ⦋1⦌)
        (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})), PinchedHom.constant x 1))))
    (r : D ⟶ A)
    (hr : r ≫ equivalenceHomotopyPathLift H hH =
      r ≫ ((prismEndpoint 0 A ≫ H) ≫ equivalencePathRefl Y)) :
    IsFunctorEqIso ((functorIsoOfEquivalenceHomotopy H hH).precomp r) := by
  have hc : IsFunctorEqIso ((equivalenceHomotopyFiberIso H hH).precomp r) := by
    exact trivialKanIso_precomp_isFunctorEqIso _ _ _ _ r hr
  have hs : IsFunctorEqIso (FunctorIso.precomp (equivalenceHomotopyFiberIso H hH).symm r) := by
    rw [functorIso_precomp_symm]
    exact hc.symm
  have hp := hs.postcomp (equivalencePathEndpoint Y 1)
  rw [functorIso_precomp_postcomp] at hp
  have h₀ : ((prismEndpoint 0 A ≫ H) ≫ equivalencePathRefl Y) ≫
      equivalencePathEndpoint Y 1 = prismEndpoint 0 A ≫ H := by
    rw [Category.assoc, equivalencePathRefl_endpoint, Category.comp_id]
  have h₁ := equivalenceHomotopyPathLift_endpoint H hH 1
  have hh := functorIso_precomp_heq_of_heq _ _ h₀ h₁
    (functorIsoOfEquivalenceHomotopy_heq H hH) r
  exact hp.of_heq (congrArg (fun k ↦ r ≫ k) h₀) (congrArg (fun k ↦ r ≫ k) h₁) hh

end SerrePositivity.InfinityCategories.F2
