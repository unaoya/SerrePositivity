module

public import SerrePositivity.KST.Spectra.ConstantKanModel
public import SerrePositivity.KST.Spectra.KanEquivalenceBridge
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.ContinuousKanSpecifiedHomotopy
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.ContinuousKanWeakEquivalence
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.WeakWhitehead

/-!
概要：離散成分への実ホモトピー切断を持つ単体集合の、Kan 置換の正次数を判定する。
方針：指定ホモトピーを Kan 置換へ移し、離散対象の置換単位とともに全基点 π 同型へ移す。
規約：元の単体集合に Kan 性を要求せず、切断と全ホモトピーを明示する。
使われ方：Sp-7 の元の分母 wide 部分複体の亜群化の離散性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Spectra

/-- 概要：離散対象への実ホモトピー切断から、Kan 置換の全正次数の類の一意性を得る。
方針：指定ホモトピーを Kan 置換へ移し、離散対象の置換単位とともに全基点 π 同型へ移す。
規約：元の単体集合に Kan 性を要求せず、切断と全ホモトピーを明示する。
使われ方：Sp-7 の元の分母 wide 部分複体の亜群化の離散性。 -/
lemma continuousKanReplacement_positive_subsingleton_of_componentRetraction
    {X : SSet.{u}} {T : Type u}
    (p : X ⟶ (Functor.const SimplexCategoryᵒᵖ).obj T)
    (s : (Functor.const SimplexCategoryᵒᵖ).obj T ⟶ X)
    (hs : s ≫ p = 𝟙 _) (H : SSet.Homotopy (p ≫ s) (𝟙 X))
    (x : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.obj X) _⦋0⦌) (n : ℕ) (hn : 0 < n) :
    Subsingleton (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.obj X) n x) := by
  let Y : SSet.{u} := (Functor.const SimplexCategoryᵒᵖ).obj T
  let : KanComplex Y := constantKanComplex T
  let : KanComplex ((𝟭 SSet.{u}).obj Y) := constantKanComplex T
  let : Quasicategory ((𝟭 SSet.{u}).obj Y) := inferInstanceAs (Quasicategory Y)
  obtain ⟨L, _⟩ := _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.continuousKanReplacement_specified_homotopy H
  have hp : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.map p) := by
    refine ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.map s, ⟨?_⟩, ⟨?_⟩⟩
    · simpa only [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id] using L
    · rw [← CategoryTheory.Functor.map_comp, hs, CategoryTheory.Functor.map_id]
      exact RelativeMorphism.Homotopy.refl _
  have hu : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app Y) := by
    have hw := _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.continuousKanReplacementUnit_isWeakHomotopyEquivalence Y
    exact hw.isSimplicialHomotopyEquivalence.isQCatEquivalence
  obtain ⟨r, hr, hs⟩ := hu
  have hi : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence r :=
    ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app Y, hs, hr⟩
  have hπ := (kanPiIsomorphism_of_qCatEquivalence _ hp.isQCatEquivalence).comp
    (kanPiIsomorphism_of_qCatEquivalence _ hi)
  let g := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.map p ≫ r
  let : Subsingleton (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy ((𝟭 SSet.{u}).obj Y) n (g.app _ x)) :=
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.constant_kanHomotopy_subsingleton T n hn (g.app _ x)
  exact Function.Injective.subsingleton ((hπ x n).1)

end SerrePositivity.KST.Spectra
