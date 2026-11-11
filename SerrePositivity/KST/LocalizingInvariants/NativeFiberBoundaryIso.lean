module

public import SerrePositivity.KST.LocalizingInvariants.NativeFiberSequence

/-!
概要：fiber 列の中央項の隣接二次数の π が零なら、同じ接続射は全単射である。
方針：元の長完全列の fiber 箇所と base 箇所の完全性をそのまま使う。
規約：同じ実四角形と接続射を保つ。Sp の安定性は使わない。
使われ方：loop 四角形の全整数次数の接続同型。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
open SerrePositivity.InfinityCategories SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.LocalizingInvariants.NativeFiber

lemma boundary_bijective_of_totalGroups (t : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroTriangle Sp.{u}) (ht : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsFiberSequence t)
    (j : ℤ) (h₀ : Subsingleton (group t 1 0 j))
    (h₁ : Subsingleton (group t 1 0 (j + 1))) : Function.Bijective (boundary t ht j) := by
  constructor
  · apply (injective_iff_map_eq_one (boundary t ht j)).2
    intro a ha
    obtain ⟨b, hb⟩ := (exact_base t ht j a).1 ha
    have hb₀ : b = 1 := h₁.elim _ _
    exact hb.symm.trans ((congrArg (right t (j + 1)) hb₀).trans (map_one _))
  · intro a
    have ha : bottom t j a = 1 := h₀.elim _ _
    exact (exact_fiber t ht j a).1 ha

end SerrePositivity.KST.LocalizingInvariants.NativeFiber
