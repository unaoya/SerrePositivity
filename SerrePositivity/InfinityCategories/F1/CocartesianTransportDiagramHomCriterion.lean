module

public import SerrePositivity.InfinityCategories.F1.CocartesianTransportDiagramHomInterval

/-!
概要：実際の区間 Hom 作用の同値性を元の Cat∞ 値分類主写像の充満忠実性へ戻す。
方針：同じ coherent Hom 比較を消去し、中間比較と厳密な分解等式を使う。
規約：区間作用の同値性は明示的な未解決の入力であり、本節だけで分類を結論しない。
使われ方：独立な Hom 同値だけから主写像の充満忠実性を誤って結論しないための接続。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories

/-- 同じ元の区間作用の同値性は、実現の実際の pinched Hom 作用の同値性を与える。 -/
lemma cocartesianTransportDiagramRealization_pinchedHomMap_isQCatEquivalence_of_homInterval
    {C : Type u} [Category.{u} C] (F G : CocartesianTransportDiagramCategory C)
    (h : IsQCatEquivalence (cocartesianTransportDiagramHomInterval F G)) :
    IsQCatEquivalence (pinchedHomMap (cocartesianTransportDiagramRealization C)
      (coherentNerveVertex F) (coherentNerveVertex G)) := by
  apply pinchedHomMap_isQCatEquivalence_of_intervalPost
    (cocartesianTransportDiagramRealization C) (coherentNerveVertex F) (coherentNerveVertex G)
    (cocartesianTransportDiagramRealization_vertex F)
    (cocartesianTransportDiagramRealization_vertex G)
  have h' := (coherentHomComparison_isQCatEquivalence F G).cancel_left h
  exact h'

/-- 全ての同じ区間作用の同値性が示せれば、実現そのものの充満忠実性が従う。 -/
lemma cocartesianTransportDiagramRealization_isFullyFaithful_of_homInterval
    (C : Type u) [Category.{u} C]
    (h : ∀ F G : CocartesianTransportDiagramCategory C,
      IsQCatEquivalence (cocartesianTransportDiagramHomInterval F G)) :
    IsFullyFaithful (cocartesianTransportDiagramRealization C) := by
  intro x y
  obtain ⟨F, rfl⟩ := (coherentNerveVertexEquiv (CocartesianTransportDiagramCategory C)).surjective x
  obtain ⟨G, rfl⟩ := (coherentNerveVertexEquiv (CocartesianTransportDiagramCategory C)).surjective y
  exact (cocartesianTransportDiagramRealization_pinchedHomMap_isQCatEquivalence_of_homInterval
    F G (h F G)).isSimplicialHomotopyEquivalence

/-- 同じ区間作用の同値性を示せば、元の分類主写像の充満忠実性を回収できる。 -/
lemma cocartesianStraighteningCoherentMap_isFullyFaithful_of_homInterval
    (C : Type u) [Category.{u} C]
    (h : ∀ F G : CocartesianTransportDiagramCategory C,
      IsQCatEquivalence (cocartesianTransportDiagramHomInterval F G)) :
    IsFullyFaithful (cocartesianStraighteningCoherentMap C) := by
  rw [← cocartesianStrictTransportInfinityMap_realization C]
  exact (cocartesianStrictTransportInfinityMap_isFullyFaithful C).comp
    (cocartesianTransportDiagramRealization_isFullyFaithful_of_homInterval C h)

end SerrePositivity.InfinityCategories
