module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.PrecompositionEquivalence
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.PrecompositionLifting

/-!
概要：前合成同値で比較した模型上の図式の延長を、元の単射に沿う厳密な延長へ移す。
方針：全体の比較で図式を戻し、部分の比較の充満忠実性で同型を戻して厳密化する。
規約：比較射そのものに単射性は不要。
使われ方：scaffold で構成した外ホーンの充填を実際の逆像へ移す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Diagrams

/-- 概要：可換四角形の両比較が前合成同値なら、模型上の図式の延長を元へ移せる。
方針：全体で本質的全射性、部分で充満忠実性を使い、単射上の同型を厳密化する。
規約：元の制限射 i のみが単射、標的 D は quasicategory。
使われ方：外ホーンの逆像上の図式の延長の模型変更。 -/
lemma exists_kanDiagramExtension_of_comparison {A B A' B' D : SSet.{u}} [Quasicategory D]
    (i : A ⟶ B) [Mono i] (j : A' ⟶ B') (a : A' ⟶ A) (b : B' ⟶ B)
    (w : a ≫ i = j ≫ b) (ha : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence a)
    (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence b) (F : A ⟶ D) (G' : B' ⟶ D)
    (hG' : j ≫ G' = a ≫ F) : ∃ G : B ⟶ D, i ≫ G = F := by
  obtain ⟨v, ⟨e⟩⟩ := (hb D).choose.isEssentiallySurjective (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex G')
  obtain ⟨G, rfl⟩ := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv B D).surjective v
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (b ≫ G) G' at e
  have ej := e.precomp j
  rw [← Category.assoc, ← w, Category.assoc, hG'] at ej
  have ef : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (i ≫ G) F := (ha D).choose.isFullyFaithful.preimageVertexIso ej
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.exists_extension_of_functorIso i G F ef

end SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Diagrams
