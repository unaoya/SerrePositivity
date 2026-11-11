module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.SequentialNerveStages
public import Mathlib.CategoryTheory.Functor.OfSequence

/-!
概要：有限段階の延長可能な条件を保つ coherent な可算全図式を構成する。
方針：条件を満たす有限図式を再帰的に選び、厳密な制限等式から全図式を貼る。
規約：各段階の条件と延長可能性を明示し、filtered 表示の存在を仮定に隠さない。
使われ方：引き戻しの交互構成で基底への指定射との整合を全段階に保持する。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-- 概要：各段階で延長可能な全図式条件を全て満たす可算図式が存在する。
方針：条件付き有限図式の列を選び、隣接段階の等式を自然変換に束ねる。
規約：有限段階の全射に関する条件を入力とし、任意の高次整合を保持する。
使われ方：基底上の交互列を有限段階から構成する一般的な再帰入口。 -/
lemma exists_sequentialDiagram_of_extensions {X : SSet.{u}}
    (P : ∀ n, ((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialNerveStage.{u} n : SSet.{u}) ⟶ X) → Prop)
    (hzero : ∃ f, P 0 f)
    (hstep : ∀ n f, P n f → ∃ g, P (n + 1) g ∧
      Subcomplex.homOfLE (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialNerveStage_monotone (Nat.le_succ n)) ≫ g = f) :
    ∃ F : nerve (ULift.{u} ℕ) ⟶ X, ∀ n, P n ((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialNerveStage n).ι ≫ F) := by
  classical
  let A n := {f : (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialNerveStage.{u} n : SSet.{u}) ⟶ X // P n f}
  let a₀ : A 0 := ⟨hzero.choose, hzero.choose_spec⟩
  let next (n : ℕ) (a : A n) : A (n + 1) :=
    ⟨(hstep n a.val a.property).choose, (hstep n a.val a.property).choose_spec.1⟩
  let a : ∀ n, A n := fun n ↦ Nat.rec a₀ next n
  have ha n : Subcomplex.homOfLE (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialNerveStage_monotone (Nat.le_succ n)) ≫
      (a (n + 1)).val = (a n).val := (hstep n (a n).val (a n).property).choose_spec.2
  let D := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialNerveStage_monotone.{u}.functor ⋙ Subcomplex.toSSetFunctor
  let η : D ⟶ (CategoryTheory.Functor.const ℕ).obj X :=
    NatTrans.ofSequence (fun n ↦ (a n).val) (fun n ↦ by
      change Subcomplex.homOfLE (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialNerveStage_monotone (Nat.le_succ n)) ≫
        (a (n + 1)).val = (a n).val ≫ 𝟙 X
      simpa only [Category.comp_id] using ha n)
  obtain ⟨F, hF⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.exists_sequentialNerve_map (fun n ↦ (a n).val) (fun n m h ↦ by
    have he := η.naturality (homOfLE h)
    change Subcomplex.homOfLE (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialNerveStage_monotone h) ≫
      (a m).val = (a n).val ≫ 𝟙 X at he
    simpa only [Category.comp_id] using he)
  refine ⟨F, fun n ↦ ?_⟩
  rw [hF n]
  exact (a n).property

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
