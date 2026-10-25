module

public import SerrePositivity.InfinityCategories.F2.Presentable.LocalObjects

/-!
概要：小さい辺族に対する既存の局所対象の全部分圏を固定する。
方針：辺族の像集合を既存の局所性述語へ渡す。
規約：元の全部分圏の定義を変更せず、同じ写像空間の前合成を使用する。
使われ方：局所対象の accessibility と反射による presentability の共通界面。
-/

@[expose] public section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable.Localization.LocalObjects
open HomotopyLimits

/-- 概要：小さい指定辺族の像に対する元の局所対象圏。
方針：既存の全部分複体をそのまま用いる。
規約：全高次単体と非可逆射を含む。
使われ方：二つの局所対象定理の対象。 -/
abbrev Category {C : SSet.{u + 1}} [Quasicategory C]
    {I : Type u} (edges : I → C _⦋1⦌) : SSet.{u + 1} :=
  (localObjectsSubcomplex (Set.range edges) : SSet.{u + 1})

/-- 概要：像集合に対する局所性は指定した全添字の前合成の同値性と同値。
方針：像集合の証人を取り出す。
規約：元の局所性と元の辺の前合成を保持する。
使われ方：端点の共通 compact 濃度で局所性を判定する。 -/
lemma isLocalObject_range_iff {C : SSet.{u + 1}} [Quasicategory C]
    {I : Type u} (edges : I → C _⦋1⦌) (z : C _⦋0⦌) :
    IsLocalObject (Set.range edges) z ↔ ∀ i,
      IsLocalForHom (Truncated.HomotopyCategory.homMk (edgeOfSimplex (edges i))) z := by
  constructor
  · intro h i
    exact h (edges i) ⟨i, rfl⟩
  · rintro h e ⟨i, rfl⟩
    exact h i

end SerrePositivity.InfinityCategories.F2.Presentable.Localization.LocalObjects
