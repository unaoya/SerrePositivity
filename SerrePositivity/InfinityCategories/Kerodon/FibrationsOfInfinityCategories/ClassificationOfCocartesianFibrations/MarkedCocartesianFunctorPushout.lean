module

public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.RelativeFunctorPushout
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.MarkedCocartesianFunctorPrecomposition
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.FullSubcomplexPullbackRestriction

/-!
概要：二つの部分が指定辺を覆う pushout で、指定辺保存 Hom も厳密に貼り合わさる。
方針：元の相対 Hom の pullback に頂点条件を課し、両制限から辺の保存を回収する。
規約：同じ元の相対関手を使い、充填性の追加仮定は置かない。
使われ方：元の cocartesian Hom の区間の貼り合わせ。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 二つの部分が全指定辺を覆えば、その二つの制限は指定辺の保存を検出する。 -/
lemma markedCocartesianFunctorPredicate_of_two_markCovers
    {E B : SSet.{u}} (q : E ⟶ B) {b c d : Over B} (i : b ⟶ d) (j : c ⟶ d)
    (V : Set (b.left _⦋1⦌)) (W : Set (c.left _⦋1⦌)) (U : Set (d.left _⦋1⦌))
    (hcover : ∀ e ∈ U,
      (∃ v ∈ V, i.left.app (Opposite.op ⦋1⦌) v = e) ∨
      (∃ w ∈ W, j.left.app (Opposite.op ⦋1⦌) w = e))
    (x : (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace q d.hom) _⦋0⦌)
    (hi : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.markedCocartesianFunctorPredicate q b.hom V
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorOverPre q i).app (Opposite.op ⦋0⦌) x))
    (hj : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.markedCocartesianFunctorPredicate q c.hom W
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorOverPre q j).app (Opposite.op ⦋0⦌) x)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.markedCocartesianFunctorPredicate q d.hom U x := by
  obtain ⟨H, hH, rfl⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.exists_relativeFunctorVertex q d.hom x
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorOverPre_vertex, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.markedCocartesianFunctorPredicate_vertex] at hi hj
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.markedCocartesianFunctorPredicate_vertex]
  intro e he
  rcases hcover e he with ⟨v, hv, rfl⟩ | ⟨w, hw, rfl⟩
  · exact hi v hv
  · exact hj w hw

/-- 指定辺を覆う pushout は、同じ指定辺保存 Hom の実際の pullback を与える。 -/
lemma markedCocartesianFunctorPre_isPullback_of_isPushout
    {E B : SSet.{u}} (q : E ⟶ B) {a b c d : Over B}
    (f : a ⟶ b) (g : a ⟶ c) (i : b ⟶ d) (j : c ⟶ d)
    (hp : IsPushout f.left g.left i.left j.left)
    (A : Set (a.left _⦋1⦌)) (V : Set (b.left _⦋1⦌))
    (W : Set (c.left _⦋1⦌)) (U : Set (d.left _⦋1⦌))
    (hf : ∀ e ∈ A, f.left.app (Opposite.op ⦋1⦌) e ∈ V)
    (hg : ∀ e ∈ A, g.left.app (Opposite.op ⦋1⦌) e ∈ W)
    (hi : ∀ e ∈ V, i.left.app (Opposite.op ⦋1⦌) e ∈ U)
    (hj : ∀ e ∈ W, j.left.app (Opposite.op ⦋1⦌) e ∈ U)
    (hcover : ∀ e ∈ U,
      (∃ v ∈ V, i.left.app (Opposite.op ⦋1⦌) v = e) ∨
      (∃ w ∈ W, j.left.app (Opposite.op ⦋1⦌) w = e)) :
    IsPullback (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.markedCocartesianFunctorPre q j W U hj)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.markedCocartesianFunctorPre q i V U hi)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.markedCocartesianFunctorPre q g A W hg)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.markedCocartesianFunctorPre q f A V hf) := by
  exact _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.isPullback_fullSubcomplex_restriction
    (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeFunctorOverPre_isPullback_of_isPushout q f g i j hp)
    _ _ _ _ _ _ _ _
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.markedCocartesianFunctorPre_ι q j W U hj)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.markedCocartesianFunctorPre_ι q i V U hi)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.markedCocartesianFunctorPre_ι q g A W hg)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.markedCocartesianFunctorPre_ι q f A V hf)
    (fun x hx hy ↦ markedCocartesianFunctorPredicate_of_two_markCovers
      q i j V W U hcover x hy hx)

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
