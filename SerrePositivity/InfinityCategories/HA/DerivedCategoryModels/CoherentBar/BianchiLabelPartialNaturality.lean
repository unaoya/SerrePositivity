module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.SubsetPartialNaturality
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.NativeLabelCoordinates
/-!
概要：末端部分集合のラベルは、その集合上で単射なら自然で、潰れれば退化する。
方針：末端を除く操作と拡張順序写像の像を比較し、部分集合の自然性を適用する。
規約：順序写像全体の単射性に制限しない。
使われ方：native 余錐の全ての退化写像での成分比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar
open CategoryTheory SSet
open scoped _root_.Simplicial

lemma dgCoherentBarWithoutLast_image_extend {m n : ℕ}
    (α : Fin (m + 1) →o Fin (n + 1)) (J : Finset (Fin (m + 2)))
    (hl : Fin.last (m + 1) ∈ J) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.withoutLast (J.image (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extendOrderHom α)) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.withoutLast J).image α := by
  calc
    _ = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.withoutLast
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.withLast (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.withoutLast J)).image
          (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extendOrderHom α)) :=
      congrArg (fun K => _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.withoutLast (K.image (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extendOrderHom α)))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.withLast_withoutLast J hl).symm
    _ = _ := by rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.image_withLast_extend, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.withoutLast_withLast]

lemma dgCoherentBarInjOn_extend_withoutLast_iff {m n : ℕ}
    (α : Fin (m + 1) →o Fin (n + 1)) (J : Finset (Fin (m + 2)))
    (hl : Fin.last (m + 1) ∈ J) :
    Set.InjOn (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extendOrderHom α) (J : Set (Fin (m + 2))) ↔
      Set.InjOn α (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.withoutLast J : Set (Fin (m + 1))) := by
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.injOn_extend_withLast_iff α (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.withoutLast J),
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.withLast_withoutLast J hl]

variable {I : SSet.{u}}

lemma dgCoherentBarBianchiLabel_map_of_injOn {m n : ℕ} (s : I _⦋n⦌)
    (α : Fin (m + 1) →o Fin (n + 1)) (J : Finset (Fin (m + 2)))
    (hJ : 2 ≤ J.card) (hb : Fin.last (m + 1) = J.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ))
    (hi : Set.InjOn (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extendOrderHom α) (J : Set (Fin (m + 2))))
    (hJ' : 2 ≤ (J.image (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extendOrderHom α)).card)
    (hb' : Fin.last (n + 1) = (J.image (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extendOrderHom α)).max'
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ')) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarBianchiLabel (I.map (SimplexCategory.mkHom α).op s) J hJ hb =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarBianchiLabel s (J.image (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extendOrderHom α)) hJ' hb' := by
  have hl : Fin.last (m + 1) ∈ J := hb ▸ J.max'_mem _
  have hiK := (dgCoherentBarInjOn_extend_withoutLast_iff α J hl).mp hi
  have hc : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.withoutLast J).card = (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.withoutLast J).card - 1 + 1 := by
    have := Finset.card_pos.mpr (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.withoutLast_nonempty hJ hl)
    omega
  have h := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarSubsetLabel_map_of_injOn s α (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.withoutLast J) hiK
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.withoutLast J).card - 1) hc
  simpa only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarBianchiLabel, dgCoherentBarWithoutLast_image_extend α J hl,
    Finset.card_image_of_injOn hiK] using h

lemma dgCoherentBarBianchiLabel_degenerate_of_not_injOn {m n : ℕ} (s : I _⦋n⦌)
    (α : Fin (m + 1) →o Fin (n + 1)) (J : Finset (Fin (m + 2)))
    (hJ : 2 ≤ J.card) (hb : Fin.last (m + 1) = J.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ))
    (hi : ¬Set.InjOn (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extendOrderHom α) (J : Set (Fin (m + 2)))) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarBianchiLabel (I.map (SimplexCategory.mkHom α).op s) J hJ hb).2 ∈
      I.degenerate (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarBianchiLabel
        (I.map (SimplexCategory.mkHom α).op s) J hJ hb).1 := by
  have hl : Fin.last (m + 1) ∈ J := hb ▸ J.max'_mem _
  exact _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarSubsetLabel_degenerate_of_not_injOn s α (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.withoutLast J)
    (hi ∘ (dgCoherentBarInjOn_extend_withoutLast_iff α J hl).mpr)
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.withoutLast J).card - 1) (by
      have := Finset.card_pos.mpr (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.withoutLast_nonempty hJ hl); omega)

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar
