module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.AWMapIndex

/-!
# AW 成分族と単調写像の可換性

概要：AW 成分族の演算は全ての面と退化による引き戻しと可換である。
方針：単射な集合では像の切断を対応させ、非単射な集合では全切断項を零とする。
規約：標準方程式はまだ仮定しない成分族の等式。
使われ方：HA 1.3.1.13、Kerodon 2.5.8（Tag 00S0） の単体的豊穣合成の自然性。

対応節は Kerodon 2.5（Tag 00ND）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u v

namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories

open CategoryTheory DifferentialGraded

variable {R : Type u} [CommRing R] {D : Type v} [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] {x y z : D}

/-- 概要：単射な集合の各切断で AW 項と引き戻しは可換である。
方針：左右の切断と像が可換であることと濃度の保存を使う。
規約：単調写像の集合全体での単射性は要求しない。
使われ方：Kerodon 2.5.8（Tag 00S0） の非退化な成分での自然性。 -/
lemma awTerm_pullback_of_inj {m n : ℕ} (α : Fin (m + 1) →o Fin (n + 1))
    (g : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData R y z n) (f : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData R x y n)
    (J : Finset (Fin (m + 1))) (j : J) (k : ℤ) (hk : k = 1 - (J.card : ℤ))
    (hi : Set.InjOn α (J : Set (Fin (m + 1)))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awTerm (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pullback α g) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pullback α f) J j k hk =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awTerm g f (J.image α) ⟨α j.val, Finset.mem_image.mpr ⟨j.val, j.property, rfl⟩⟩ k
        (by rw [Finset.card_image_of_injOn hi]; exact hk) := by
  have hl : Set.InjOn α ((J.filter (· ≤ j.val) : Finset _) : Set _) :=
    hi.mono (fun _ ha ↦ (Finset.mem_filter.mp ha).1)
  have hr : Set.InjOn α ((J.filter (j.val ≤ ·) : Finset _) : Set _) :=
    hi.mono (fun _ ha ↦ (Finset.mem_filter.mp ha).1)
  have hcl : (J.filter (· ≤ j.val)).card = ((J.image α).filter (· ≤ α j.val)).card := by
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.AWMapIndex.image_left α.monotone hi j.property, Finset.card_image_of_injOn hl]
  have hcr : (J.filter (j.val ≤ ·)).card = ((J.image α).filter (α j.val ≤ ·)).card := by
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.AWMapIndex.image_right α.monotone hi j.property, Finset.card_image_of_injOn hr]
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awTerm
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pullback_component_of_inj _ _ _ _ _ _ hl,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pullback_component_of_inj _ _ _ _ _ _ hr]
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.AWAssocTerms.compose_eq_of_heq
  · exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.component_heq_of_eq g _ _ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.AWMapIndex.image_left α.monotone hi j.property) _ _ _ _ _ _
  · exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.component_heq_of_eq f _ _ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.AWMapIndex.image_right α.monotone hi j.property) _ _ _ _ _ _
  · rw [hcr]
  · rw [hcl]

/-- 概要：非単射な集合の各切断で引き戻した成分族の AW 項は零である。
方針：左右の切断がともに単射なら全体も単射となるため、少なくとも片側が零である。
規約：端点での切断も含む。
使われ方：Kerodon 2.5.8（Tag 00S0） の退化な成分での自然性。 -/
lemma awTerm_pullback_of_not_inj {m n : ℕ} (α : Fin (m + 1) →o Fin (n + 1))
    (g : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData R y z n) (f : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData R x y n)
    (J : Finset (Fin (m + 1))) (j : J) (k : ℤ) (hk : k = 1 - (J.card : ℤ))
    (hi : ¬ Set.InjOn α (J : Set (Fin (m + 1)))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awTerm (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pullback α g) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pullback α f) J j k hk = 0 := by
  by_cases hl : Set.InjOn α ((J.filter (· ≤ j.val) : Finset _) : Set _)
  · have hr : ¬ Set.InjOn α ((J.filter (j.val ≤ ·) : Finset _) : Set _) :=
      fun hr ↦ hi (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.AWMapIndex.injOn_of_cuts α.monotone j.property hl hr)
    unfold _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awTerm
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pullback_component_of_not_inj _ _ _ _ _ _ hr]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.compose_zero _ _
  · unfold _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awTerm
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pullback_component_of_not_inj _ _ _ _ _ _ hl]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.zero_compose _ _

/-- 概要：単射な集合とその像の切断点の型は同値である。
方針：単射写像を部分集合の元の型へ制限し、像の元の逆像を取る。
規約：有限集合上の単射性だけを使う。
使われ方：Kerodon 2.5.8（Tag 00S0） の AW の和の添字の移送。 -/
def awImageEquiv {m n : ℕ} (α : Fin (m + 1) →o Fin (n + 1))
    (J : Finset (Fin (m + 1))) (hi : Set.InjOn α (J : Set (Fin (m + 1)))) :
    J ≃ ↥(J.image α) :=
  Equiv.ofBijective (fun j ↦ ⟨α j.val, Finset.mem_image.mpr ⟨j.val, j.property, rfl⟩⟩)
    ⟨fun a b h ↦ Subtype.ext (hi a.property b.property (congrArg Subtype.val h)), by
      rintro ⟨b, hb⟩
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hb
      exact ⟨⟨a, ha⟩, rfl⟩⟩

/-- 概要：AW 成分族の合成は全ての単調写像による引き戻しと可換である。
方針：単射な集合では切断点の和を像で移し、非単射な集合では両辺を零とする。
規約：全ての面と退化を含む単体的自然性を述べる。
使われ方：HA 1.3.1.13、Kerodon 2.5.8（Tag 00S0） の単体的豊穣合成の可換性。 -/
lemma awData_pullback {m n : ℕ} (α : Fin (m + 1) →o Fin (n + 1))
    (g : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData R y z n) (f : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData R x y n) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pullback α (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awData g f) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awData (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pullback α g) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pullback α f) := by
  funext a
  rcases a with ⟨⟨J, k⟩, hJ, hk⟩
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pullback α (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awData g f)).component J k hJ hk =
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awData (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pullback α g) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pullback α f)).component J k hJ hk
  by_cases hi : Set.InjOn α (J : Set (Fin (m + 1)))
  · rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pullback_component_of_inj _ _ _ _ _ _ hi,
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awData_component, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awData_component]
    symm
    apply Fintype.sum_equiv (awImageEquiv α J hi)
    intro j
    exact awTerm_pullback_of_inj α g f J j k hk hi
  · rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pullback_component_of_not_inj _ _ _ _ _ _ hi, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awData_component]
    symm
    apply Finset.sum_eq_zero
    intro j _
    exact awTerm_pullback_of_not_inj α g f J j k hk hi

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
