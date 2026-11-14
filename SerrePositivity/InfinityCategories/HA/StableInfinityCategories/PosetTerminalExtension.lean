module
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.VertexTransport.VertexPrescribedExtension

/-!
概要：順序部分型の図式を元の順序集合へ厳密に延長する。
方針：全部分複体の同型と、有限局所余極限・指定終対象への延長を接続する。
規約：元の図式と指定した終対象を保持する。使われ方：一般安定性判定の比較格子。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-- 元の順序部分型の全図式を厳密に保持する比較。 -/
lemma exists_poset_downward_terminal_extension {P : Type u} [PartialOrder P]
    (T : P → Prop) (hT : ∀ {a b : P}, a ≤ b → T b → T a)
    {X : SSet.{u}}
    (G : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices (nerve P) (fun v ↦ T (nerveEquiv v)) : SSet.{u}) ⟶ X)
    (z : X _⦋0⦌) (hz : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex z) :
    ∃ F : nerve P ⟶ X,
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices (nerve P) (fun v ↦ T (nerveEquiv v))).ι ≫ F = G ∧
        ∀ v, ¬ T (nerveEquiv v) → F.app (Opposite.op ⦋0⦌) v = z := by
  classical
  let A := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices (nerve P) (fun v ↦ T (nerveEquiv v))
  let w (v : (nerve P) _⦋0⦌) (hv : T (nerveEquiv v)) : (A : SSet.{u}) _⦋0⦌ :=
    ⟨v, by
      intro f
      have hf : f = 𝟙 ⦋0⦌ := Subsingleton.elim _ _
      simpa only [hf, op_id, CategoryTheory.Functor.map_id_apply] using hv⟩
  let x (v : (nerve P) _⦋0⦌) : X _⦋0⦌ :=
    if hv : T (nerveEquiv v) then G.app (Opposite.op ⦋0⦌) (w v hv) else z
  obtain ⟨F, hF, hv⟩ := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.exists_extension_with_vertices A G x
    (by
      intro v
      dsimp only [x]
      rw [dite_eq_left (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex v)]
      rfl)
    (by
      intro n s hs
      have hn : ¬ T (nerveEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.simplexLastVertex s)) := by
        intro h
        apply hs
        intro v
        change T (s.obj (v.toOrderHom 0))
        exact hT (s.monotone (Fin.le_last _)) h
      right
      dsimp only [x]
      rw [dite_eq_right hn]
      exact hz)
  refine ⟨F, hF, ?_⟩
  intro v hn
  rw [hv]
  exact dite_eq_right hn

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
