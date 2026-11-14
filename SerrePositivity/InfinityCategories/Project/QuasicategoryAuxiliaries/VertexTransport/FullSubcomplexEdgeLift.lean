module
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TerminalVertices
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.MappingSpaces.FiniteShapes

/-! # 全部分単体集合への辺の持ち上げ

概要：全部分単体集合の二頂点間の辺は、元の辺を変えずに全部分単体集合へ持ち上がる。
方針：一次元標準単体の二頂点の条件を検査し、全部分複体への持ち上げを使う。
規約：quasicategory 性は不要。
使われ方：S4 の普遍余錐間の比較ホモトピーを普遍余錐全体の辺として扱う。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries

/-- 概要：全部分単体集合の二頂点間の辺を持ち上げ、包含で元の辺へ戻す。
方針：辺の二端点が頂点条件を満たすことから標準単体全体を持ち上げる。
規約：元の単体集合への仮定なし。使われ方：普遍余錐の辺の表示。 -/
lemma exists_fullSubcomplexEdgeLift {X : SSet.{u}} (P : X _⦋0⦌ → Prop)
    (a b : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices X P : SSet.{u}) _⦋0⦌)
    (e : SSet.Truncated.Edge (X := (truncation 2).obj X) a.val b.val) :
    ∃ f : SSet.Truncated.Edge
      (X := (truncation 2).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices X P : SSet.{u})) a b,
      f.map ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices X P).ι) = e := by
  let E : (Δ[1] : SSet.{u}) ⟶ X := SSet.yonedaEquiv.symm e.edge
  have h₀ : stdSimplex.δ (1 : Fin 2) ≫ E = SSet.yonedaEquiv.symm a.val := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.edgeSimplex_source e
  have h₁ : stdSimplex.δ (0 : Fin 2) ≫ E = SSet.yonedaEquiv.symm b.val := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.edgeSimplex_target e
  have hp₀ : SSet.yonedaEquiv (stdSimplex.δ (1 : Fin 2) : (Δ[0] : SSet.{u}) ⟶ Δ[1]) =
      stdSimplex.obj₀Equiv.symm (0 : Fin 2) := by decide
  have hp₁ : SSet.yonedaEquiv (stdSimplex.δ (0 : Fin 2) : (Δ[0] : SSet.{u}) ⟶ Δ[1]) =
      stdSimplex.obj₀Equiv.symm (1 : Fin 2) := by decide
  have hv : ∀ v : (Δ[1] : SSet.{u}) _⦋0⦌, P (E.app (Opposite.op ⦋0⦌) v) := by
    intro v
    obtain ⟨i, rfl⟩ := stdSimplex.obj₀Equiv.symm.surjective v
    fin_cases i
    · change P (E.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (0 : Fin 2)))
      have h := congrArg SSet.yonedaEquiv h₀
      simp only [SSet.yonedaEquiv_comp, hp₀, Equiv.apply_symm_apply] at h
      rw [h]
      exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex a
    · change P (E.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (1 : Fin 2)))
      have h := congrArg SSet.yonedaEquiv h₁
      simp only [SSet.yonedaEquiv_comp, hp₁, Equiv.apply_symm_apply] at h
      rw [h]
      exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex b
  let F := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift P E hv
  let f : SSet.Truncated.Edge
      (X := (truncation 2).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices X P : SSet.{u})) a b := {
    edge := SSet.yonedaEquiv F
    src_eq := by
      apply Subtype.ext
      change X.δ 1 (SSet.yonedaEquiv E) = a.val
      rw [← stdSimplex.yonedaEquiv_δ_comp, h₀]
      exact SSet.yonedaEquiv.apply_symm_apply a.val
    tgt_eq := by
      apply Subtype.ext
      change X.δ 0 (SSet.yonedaEquiv E) = b.val
      rw [← stdSimplex.yonedaEquiv_δ_comp, h₁]
      exact SSet.yonedaEquiv.apply_symm_apply b.val }
  refine ⟨f, SSet.Truncated.Edge.ext ?_⟩
  change SSet.yonedaEquiv E = e.edge
  exact SSet.yonedaEquiv.apply_symm_apply e.edge

end SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries
