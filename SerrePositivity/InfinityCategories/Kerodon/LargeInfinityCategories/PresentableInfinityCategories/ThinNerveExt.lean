module
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.CategoryTheory.WithTerminal.Basic

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join

/-!
概要：thin 圏の nerve への二つの射は、元の全頂点で一致すれば全単体で一致する。
方針：単体作用素で各射列の対象を回収し、thin 性で射の成分を一意にする。
規約：始域は任意の単体集合。標的の thin 性を明示する。
使われ方：濃度変更で使う poset の二つの錐添字模型の比較。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-- thin 圏の nerve への射は、全頂点での作用によって一意に決まる。 -/
lemma thinNerve_hom_ext {C : Type u} [SmallCategory C] [Quiver.IsThin C]
    {K : SSet.{u}} {f g : K ⟶ nerve C}
    (h : ∀ x : K _⦋0⦌, f.app (Opposite.op ⦋0⦌) x = g.app (Opposite.op ⦋0⦌) x) :
    f = g := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro s
  refine ComposableArrows.ext (fun i ↦ ?_) (fun _ _ ↦ Subsingleton.elim _ _)
  let a : ⦋0⦌ ⟶ ⦋n⦌ := SimplexCategory.Hom.mk (OrderHom.const _ i)
  have hf := ConcreteCategory.congr_hom (f.naturality a.op) s
  have hg := ConcreteCategory.congr_hom (g.naturality a.op) s
  exact congrArg (fun t : (nerve C) _⦋0⦌ ↦ t.obj 0)
    (hf.symm.trans ((h (K.map a.op s)).trans hg))

/-- 始対象を付加しても、元の thin 性は保たれる。 -/
lemma withInitial_isThin (C : Type u) [SmallCategory C] [Quiver.IsThin C] :
    Quiver.IsThin (WithInitial C) := fun x y ↦ by
  cases x <;> cases y
  all_goals
    change Subsingleton (WithInitial.Hom _ _)
    dsimp only [WithInitial.Hom]
    infer_instance

/-- thin な nerve への join の射は、左右の包含上で一致すれば全単体で一致する。 -/
lemma thinNerve_join_hom_ext {C : Type u} [SmallCategory C] [Quiver.IsThin C]
    {A B : SSet.{u}} {f g : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join A B ⟶ nerve C}
    (hA : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl A B ≫ f = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl A B ≫ g)
    (hB : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr A B ≫ f = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr A B ≫ g) : f = g := by
  apply thinNerve_hom_ext
  rintro ⟨ℓ, x, y⟩
  fin_cases ℓ
  · cases x
    exact ConcreteCategory.congr_hom (NatTrans.congr_app hB (Opposite.op ⦋0⦌)) y
  · cases y
    exact ConcreteCategory.congr_hom (NatTrans.congr_app hA (Opposite.op ⦋0⦌)) x

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
