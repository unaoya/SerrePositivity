module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.CoslicePostcompTransport

/-!
概要：元の頂点の coslice の後合成は同じ恒等錐を厳密に保持する。
方針：固定図式の等号による輸送を全錐の射の値で消し、定値射の後合成を計算する。
規約：既存の正規化済み後合成をそのまま使う。
使われ方：全解の輸送と coslice 射影を同じ始対象で照合する。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-- 概要：指定頂点の像で正規化した coslice の後合成は恒等錐を保持する。
方針：固定図式の等号輸送が元の全射を変えないことを使う。
規約：関手に fibration 性や同値性を要求しない。
使われ方：coslice の始対象における解の輸送の一致。 -/
lemma coslicePostcomp_identity {X Y : SSet.{u}} (f : X ⟶ Y) (x : X _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.stableCoslicePostcomp (SSet.yonedaEquiv.symm x) f
      (SSet.yonedaEquiv.symm (f.app (Opposite.op ⦋0⦌) x))
      (SSet.yonedaEquiv_symm_comp x f)).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.cosliceIdentityCone x) =
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.cosliceIdentityCone (f.app (Opposite.op ⦋0⦌) x) := by
  have hv {K X Y : SSet.{u}} (a : K ⟶ X) (f : X ⟶ Y) (b : K ⟶ Y)
      (h : a ≫ f = b) (s : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder a) _⦋0⦌) :
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.stableCoslicePostcomp a f b h).app (Opposite.op ⦋0⦌) s).val = s.val ≫ f := by
    subst b
    rfl
  apply Subtype.ext
  rw [hv]
  exact SSet.const_comp x f

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
