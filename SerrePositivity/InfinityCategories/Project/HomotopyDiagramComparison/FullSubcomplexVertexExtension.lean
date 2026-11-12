module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.InnerFibrations.FullSubcomplexFibration

/-!
概要：頂点を全て含む境界に沿って、元の全部分複体への写像を厳密に延長する。
方針：周囲の延長の各頂点の所属を境界から回収し、元の頂点条件で持ち上げる。
規約：元の境界写像と周囲の全写像を保持する。充填性は不要。
使われ方：元の前層余極限性を P_Σ の全部分複体へ反映する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison

/-- 周囲の延長の全頂点が元の境界で被覆されるなら、元の全部分複体へ厳密に延長。 -/
lemma fullSubcomplex_vertex_extension {A B X : SSet.{u}} (P : X _⦋0⦌ → Prop)
    (i : A ⟶ B) (hi : Function.Surjective (i.app (Opposite.op ⦋0⦌)))
    (a : A ⟶ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices X P : SSet.{u})) (b : B ⟶ X)
    (h : i ≫ b = a ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices X P).ι) :
    ∃ l : B ⟶ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices X P : SSet.{u}),
      i ≫ l = a ∧ l ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices X P).ι = b := by
  have hv : ∀ v : B _⦋0⦌, P (b.app (Opposite.op ⦋0⦌) v) := by
    intro v
    obtain ⟨w, rfl⟩ := hi v
    have H := congrArg (fun f => f.app (Opposite.op ⦋0⦌) w) h
    change b.app _ (i.app _ w) = (a.app _ w).val at H
    rw [H]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex (a.app _ w)
  refine ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift P b hv, ?_, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift_ι P b hv⟩
  apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices X P).ι).1
  rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift_ι]
  exact h

end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
