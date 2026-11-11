module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.FixedSourceFactorization
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.RelativeAlternatingDiagram

/-!
概要：固定入力図式を保持する相対交互構成の前置段と極限貼り合わせ。
方針：全図式を固定入力図式の coslice 内に持ち上げる。
規約：元の両成分表示を変更せず入力の全単体を保つ。
使われ方：compact 成分対の comma における全小図式の延長。

対応節は Kerodon 9.4（Tag 06GT）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility

variable {κ : Cardinal.{u}} {K : SSet.{u}} {B : SSet.{u + 1}}
  {x : (Δ[0] : SSet.{u + 1}) ⟶ B} {I : Fin 2 → SSet.{u}}
  {P : ∀ c, (SSet.uliftFunctor.{u + 1, u}).obj (I c) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver x}

/-- 概要：固定入力図式を保持する閉前置段。
方針：元の閉前置段の全図式を固定入力の下へ持ち上げる。
規約：同じ成分表示と元の全射影を保持する。
使われ方：入力付き相対塔の各段。 -/
structure SeededAlternatingClosedStage
    (z : (SSet.uliftFunctor.{u + 1, u}).obj K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver x) (a : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.AlternatingIndex κ) where
  stage : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.RelativeAlternatingClosedStage κ x I P a
  under : (SSet.uliftFunctor.{u + 1, u}).obj
    (nerve {b : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.AlternatingIndex κ // b ≤ a}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder z
  projection : under ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection z = stage.diagram

/-- 概要：固定入力図式を保持する厳密前置段。
方針：元の厳密前置段の全図式を固定入力の下へ持ち上げる。
規約：同じ成分表示と元の全射影を保持する。
使われ方：入力付き相対因子化の前置入力。 -/
structure SeededAlternatingOpenStage
    (z : (SSet.uliftFunctor.{u + 1, u}).obj K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver x) (a : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.AlternatingIndex κ) where
  stage : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.RelativeAlternatingOpenStage κ x I P a
  under : (SSet.uliftFunctor.{u + 1, u}).obj (nerve (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.AlternatingLower κ a)) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder z
  projection : under ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection z = stage.diagram

/-- 概要：固定入力付き閉前置段の全過去段への制限。
方針：元の段の整合と固定入力の下での全図式の整合を同時に要求する。
規約：全単体上の厳密な等式。
使われ方：全前置段の well-founded 選択。 -/
def SeededAlternatingClosedStage.Restricts
    {z : (SSet.uliftFunctor.{u + 1, u}).obj K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver x} {a b : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.AlternatingIndex κ}
    (s : SeededAlternatingClosedStage (κ := κ) (I := I) (P := P) z a)
    (t : SeededAlternatingClosedStage (κ := κ) (I := I) (P := P) z b) : Prop :=
  s.stage.Restricts t.stage ∧ ∀ h : a ≤ b,
    (SSet.uliftFunctor.{u + 1, u}).map (nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.closedPrefixMap h)) ≫ t.under = s.under

/-- 概要：固定入力付き厳密前置段の全過去閉前置段への制限。
方針：元の段の保持条件と固定入力の下での制限を同時に記録する。
規約：元の両成分表示と入力の全単体を保持する。
使われ方：入力付きの一段延長から全過去整合を回収する。 -/
def SeededAlternatingOpenStage.Preserves
    {z : (SSet.uliftFunctor.{u + 1, u}).obj K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver x} {a b : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.AlternatingIndex κ}
    (s : SeededAlternatingOpenStage (κ := κ) (I := I) (P := P) z a) (hb : b < a)
    (t : SeededAlternatingClosedStage (κ := κ) (I := I) (P := P) z b) : Prop :=
  s.stage.Preserves hb t.stage ∧
    (SSet.uliftFunctor.{u + 1, u}).map (nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.closedPrefixIntoStrict a ⟨b, hb⟩)) ≫
      s.under = t.under

/-- 概要：整合する全過去の入力付き閉前置段は、現在の入力付き厳密前置段へ貼り合わさる。
方針：固定入力の coslice 内で全図式を貼り合わせ、元の表示添字を保持する。
規約：極限位置にも終頂点や入力図式の余極限を要求しない。
使われ方：入力付き相対交互構成の各再帰段。 -/
lemma exists_seededAlternatingOpenStage_preserving
    {z : (SSet.uliftFunctor.{u + 1, u}).obj K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver x}
    (a : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.AlternatingIndex κ)
    (prev : ∀ b : {i : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.AlternatingIndex κ // i < a},
      SeededAlternatingClosedStage (κ := κ) (I := I) (P := P) z b.val)
    (hprev : ∀ b d : {i : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.AlternatingIndex κ // i < a},
      b < d → (prev b).Restricts (prev d)) :
    ∃ s : SeededAlternatingOpenStage (κ := κ) (I := I) (P := P) z a,
      ∀ b : {i : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.AlternatingIndex κ // i < a}, s.Preserves b.property (prev b) := by
  have hdiagram : ∀ (b d : {i : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.AlternatingIndex κ // i < a}) (h : b ≤ d),
      (SSet.uliftFunctor.{u + 1, u}).map
        (nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.closedPrefixMap (I := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.AlternatingIndex κ) (a := b.val) (b := d.val) h)) ≫
        (prev d).under = (prev b).under := by
    intro b d h
    rcases h.lt_or_eq with h | rfl
    · exact (hprev b d h).2 h.le
    · change (SSet.uliftFunctor.{u + 1, u}).map (𝟙 _) ≫ _ = _
      rw [(SSet.uliftFunctor.{u + 1, u}).map_id, Category.id_comp]
  obtain ⟨s, hs⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.exists_relativeAlternatingOpenStage_preserving a
    (fun b ↦ (prev b).stage) (fun b d h ↦ (hprev b d h).1)
  obtain ⟨R, hR⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.exists_strictPrefixGluing a (fun b ↦ (prev b).under) hdiagram
  have hcomp : ∀ c, (SSet.uliftFunctor.{u + 1, u}).map
      (nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.alternatingLowerSection κ a c)) ≫ (R ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection z) =
      (SSet.uliftFunctor.{u + 1, u}).map (s.index c) ≫ P c := by
    intro c
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.componentPrefix_ulift_hom_ext a c
    intro b
    calc
      _ = (SSet.uliftFunctor.{u + 1, u}).map
          (nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.alternatingClosedSection κ b.val c)) ≫
          ((SSet.uliftFunctor.{u + 1, u}).map
            (nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.closedPrefixIntoStrict a b)) ≫ R) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection z := rfl
      _ = (SSet.uliftFunctor.{u + 1, u}).map ((prev b).stage.index c) ≫ P c := by
        rw [hR b, (prev b).projection, (prev b).stage.component_eq c]
      _ = _ := by
        rw [← Category.assoc, ← CategoryTheory.Functor.map_comp, (hs b).2 c]
  let S : SeededAlternatingOpenStage (κ := κ) (I := I) (P := P) z a :=
    ⟨⟨s.index, R ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection z, hcomp⟩, R, rfl⟩
  refine ⟨S, ?_⟩
  intro b
  refine ⟨⟨?_, (hs b).2⟩, hR b⟩
  change (SSet.uliftFunctor.{u + 1, u}).map
    (nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.closedPrefixIntoStrict a b)) ≫ (R ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection z) = (prev b).stage.diagram
  rw [← Category.assoc, hR b, (prev b).projection]

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility
