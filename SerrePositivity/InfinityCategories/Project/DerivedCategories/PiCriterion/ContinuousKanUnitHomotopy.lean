module

public import SerrePositivity.InfinityCategories.Project.FilteredExchange.ContinuousKanHomotopy
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.WeakWhitehead
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.HomotopyBoundaryExtension

/-!
概要：Kan 対象への射のホモトピーは連続置換の単位による後合成で反映される。
方針：単位の実際のホモトピー逆を使い、写像空間の連結成分で消去する。
規約：パラメータの始域に充填性・有限性を要求しない。
使われ方：一つの fiber の置換内で検出した有限ホモトピーを元の fiber に戻す。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.PiCriterion

/-- 概要：Kan 対象への二射は、その単位による像がホモトピックなら元もホモトピック。
方針：単位の左ホモトピー逆で後合成した三つのホモトピー類を合成する。
規約：全パラメータで反映する。使われ方：fiber 内のホモトピー検出。 -/
lemma continuousKanReplacementUnit_reflects_homotopy {A X : SSet.{u}} [KanComplex X]
    {f g : A ⟶ X} (H : SSet.Homotopy (f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app X)
      (g ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app X)) : Nonempty (SSet.Homotopy f g) := by
  let η : X ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.obj X := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app X
  have hw : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence η := _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.continuousKanReplacementUnit_isWeakHomotopyEquivalence X
  obtain ⟨r, ⟨Hr⟩, _⟩ := hw.isSimplicialHomotopyEquivalence
  have h := (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex_piZero_eq_iff_homotopy _ _).2 ⟨_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp H r⟩
  have hf := (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex_piZero_eq_iff_homotopy _ _).2 ⟨_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp Hr f⟩
  have hg := (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex_piZero_eq_iff_homotopy _ _).2 ⟨_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp Hr g⟩
  simp only [Category.assoc, Category.comp_id] at h hf hg
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex_piZero_eq_iff_homotopy _ _).1 (hf.symm.trans (h.trans hg))

/-- 概要：Kan 対象の指定境界の充填は単位による後合成で反映される。
方針：単位の逆で充填を戻し、逆合成の関手同型に沿って境界を戻す。
規約：零次元の空境界も含む。使われ方：置換した fiber 内の充填の検出。 -/
lemma continuousKanReplacementUnit_reflects_boundaryFilling {X : SSet.{u}} [KanComplex X]
    (n : ℕ) (a : (boundary n : SSet.{u}) ⟶ X)
    (h : ∃ w : (Δ[n] : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.obj X,
      (boundary n).ι ≫ w = a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app X) :
    ∃ w : (Δ[n] : SSet.{u}) ⟶ X, (boundary n).ι ≫ w = a := by
  let η : X ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.obj X := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app X
  have hw : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence η := _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.continuousKanReplacementUnit_isWeakHomotopyEquivalence X
  obtain ⟨r, ⟨e⟩, _⟩ := hw.isSimplicialHomotopyEquivalence.isQCatEquivalence
  have he : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (a ≫ (η ≫ r)) a := by
    simpa only [Category.comp_id] using _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.precomp e a
  apply he.exists_boundaryFilling
  obtain ⟨w, hw⟩ := h
  exact ⟨w ≫ r, by rw [← Category.assoc, hw, Category.assoc]⟩

end SerrePositivity.InfinityCategories.Project.DerivedCategories.PiCriterion
