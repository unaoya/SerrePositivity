module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGCoherentBarBianchiFullTerms
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGCoherentBarSubsetNaturality
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedReindexIndex

/-!
概要：bar を末端に加えた係数のラベルは、先頭頂点の単射な制限と厳密に両立する。
方針：最終点固定の延長による像から先頭集合を回収し、元の部分単体の自然性を使う。
規約：実単体ラベルの等号を保持する。
使われ方：全体 HA 右辺の比較を任意の部分集合へ制限する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory SSet
open scoped _root_.Simplicial

lemma dgCoherentBarExtend_injective {m n : ℕ}
    (α : Fin (m + 1) →o Fin (n + 1)) (hα : Function.Injective α) :
    Function.Injective (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extendOrderHom α) := by
  have hh := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.injOn_extend_withLast_iff α Finset.univ).mpr hα.injOn
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBar_withLast_univ] at hh
  exact fun a b hab => hh (Finset.mem_univ _) (Finset.mem_univ _) hab

variable {I : SSet.{u}}

lemma dgCoherentBarBianchiLabel_map {m n : ℕ} (σ : I _⦋n⦌)
    (α : Fin (m + 1) →o Fin (n + 1)) (hα : Function.Injective α)
    (J : Finset (Fin (m + 2))) (hJ : 2 ≤ J.card)
    (hb : Fin.last (m + 1) = J.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ))
    (hJ' : 2 ≤ (J.image (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extendOrderHom α)).card)
    (hb' : Fin.last (n + 1) = (J.image (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extendOrderHom α)).max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ')) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarBianchiLabel (I.map (SimplexCategory.mkHom α).op σ) J hJ hb =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarBianchiLabel σ (J.image (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extendOrderHom α)) hJ' hb' := by
  have hLast : Fin.last (m + 1) ∈ J := hb ▸ J.max'_mem _
  have hK : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.withoutLast (J.image (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extendOrderHom α)) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.withoutLast J).image α := by
    calc
      _ = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.withoutLast
          ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.withLast (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.withoutLast J)).image
            (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extendOrderHom α)) :=
        congrArg (fun S => _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.withoutLast (S.image (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extendOrderHom α)))
          (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.withLast_withoutLast J hLast).symm
      _ = _ := by rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.image_withLast_extend, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.withoutLast_withLast]
  have hcard : ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.withoutLast J).image α).card =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.withoutLast J).card := Finset.card_image_of_injective _ hα
  have hc : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.withoutLast J).card =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.withoutLast J).card - 1 + 1 := by
    have := Finset.card_pos.mpr (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.withoutLast_nonempty hJ hLast)
    omega
  have hh := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSubsetLabel_map σ α hα (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.withoutLast J)
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.withoutLast J).card - 1) hc
  simpa only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarBianchiLabel, hK, hcard] using hh

end SerrePositivity.InfinityCategories.Project.DerivedCategories
