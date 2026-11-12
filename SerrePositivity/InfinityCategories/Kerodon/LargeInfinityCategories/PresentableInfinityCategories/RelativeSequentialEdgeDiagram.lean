module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.RelativeSequentialEdgeSimplices

/-!
概要：任意の指定辺列を、指定された基底の全可算図式の上で実現する。
方針：基底を保つ有限全単体列を貼り合わせ、始区間による全射の検出を使う。
規約：辺のホモトピー類や射影の点ごとの一致で代用しない。
使われ方：引き戻しの compact 表示を元の対象の上で同期する。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-- 概要：指定辺列と基底の全可算図式を同時に保つ一つの全図式が存在する。
方針：全有限始区間での相対延長を貼り合わせる。
規約：射は inner fibration。余極限・filtered 性を仮定しない。
使われ方：引き戻しの交互構成で必要な基底上の高次整合。 -/
lemma exists_relativeSequentialDiagram_realizing_edges {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] (p : X ⟶ Y) [InnerFibration p]
    (x : ℕ → X _⦋0⦌) (e : ∀ n, X.Edge (x n) (x (n + 1)))
    (H : nerve (ULift.{u} ℕ) ⟶ Y)
    (he : ∀ n, SSet.yonedaEquiv.symm (e n).edge ≫ p =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialNerveSuccessorEdge n ≫ H) :
    ∃ F : nerve (ULift.{u} ℕ) ⟶ X, F ≫ p = H ∧ ∀ n,
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialNerveSuccessorEdge n ≫ F = SSet.yonedaEquiv.symm (e n).edge := by
  obtain ⟨f, hzero, hf, hp, hedge⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.exists_relativeSequentialEdgeSimplices p x e H he
  obtain ⟨F, hF⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.exists_sequentialDiagram_of_simplices f hf
  refine ⟨F, ?_, fun n ↦ ?_⟩
  · apply _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialNerve_hom_ext_initialSimplex
    intro n
    dsimp only [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialNerveInitialSimplex]
    rw [← Category.assoc, Category.assoc _ _ F, hF, Iso.inv_hom_id_assoc]
    exact hp n
  · cases n with
    | zero =>
      simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialNerveSuccessorEdge, Category.assoc, hF,
        Iso.inv_hom_id_assoc, hzero]
    | succ n =>
      simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialNerveSuccessorEdge, Category.assoc, hF, Iso.inv_hom_id_assoc]
      exact hedge n

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
