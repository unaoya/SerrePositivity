module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.ContinuousKanAnodyne
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.ContinuousKanFilling
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.ContinuousKanSequence
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.HomotopyWhiskering
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.AnodyneHomotopyExtension

/-!
概要：連続 Kan 置換後のホモトピーを、元の指定円柱の像に厳密に延長する。
方針：単位の自然性で両端を照合し、anodyne な単位に沿って円柱を延長する。
規約：Q を単体的豊穣関手と仮定せず、必要な相対延長を選ぶ。
使われ方：有限標的図式の輸送を元の境界円柱とともに Kan 置換内へ移す。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.FilteredExchange

/-- 概要：元の全円柱を保つ Kan 置換後の比較ホモトピーが存在する。
方針：両端の自然性を持つ明示的な円柱を単位に沿って延長する。
規約：単位への制限は元の円柱の像そのもの。使われ方：指定境界輸送の全時刻での保持。 -/
lemma continuousKanReplacement_specified_homotopy {A X : SSet.{u}} {f g : A ⟶ X}
    (H : SSet.Homotopy f g) :
    ∃ L : SSet.Homotopy (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.map f) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.map g),
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app A ▷ (Δ[1] : SSet.{u})) ≫ L.h =
        H.h ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app X := by
  let h : SSet.Homotopy
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app A ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.map f)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app A ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.map g) :=
    { h := H.h ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app X
      h₀ := by
        rw [← Category.assoc, H.h₀]
        exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.naturality f
      h₁ := by
        rw [← Category.assoc, H.h₁]
        exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.naturality g
      rel := by
        apply SSet.hom_ext
        intro n
        apply ConcreteCategory.hom_ext
        intro x
        exact False.elim x.1.property }
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.anodyne_homotopy_extension (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app A)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit_anodyne A) _ _ h

/-- 概要：指定図式の単位に境界が因子分解すれば、その全境界円柱を延長後も保持できる。
方針：指定円柱の延長を前合成し、境界の因子分解と単位上の式を使う。
規約：境界射の単射性は不要。使われ方：有限 path 模型の輸送円柱の境界。 -/
lemma continuousKanReplacement_specified_homotopy_precomp {A M K X : SSet.{u}}
    {f g : M ⟶ X} (H : SSet.Homotopy f g) (i : A ⟶ K) (m : A ⟶ M)
    (z : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.obj M)
    (hz : i ≫ z = m ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app M) :
    ∃ G : SSet.Homotopy (z ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.map f)
      (z ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.map g),
      (i ▷ (Δ[1] : SSet.{u})) ≫ G.h =
        (m ▷ (Δ[1] : SSet.{u})) ≫ H.h ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app X := by
  obtain ⟨L, hL⟩ := continuousKanReplacement_specified_homotopy H
  refine ⟨_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp L z, ?_⟩
  change (i ▷ (Δ[1] : SSet.{u})) ≫ (z ▷ (Δ[1] : SSet.{u})) ≫ L.h = _
  rw [← comp_whiskerRight_assoc, hz, comp_whiskerRight, Category.assoc, hL]

end SerrePositivity.InfinityCategories.Project.FilteredExchange
