module
public import SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FromCategoriesToSimplicialSets.GroupNerveHomotopy

public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.CoreFlag.StrictSegalHomotopy
public import SerrePositivity.KST.Spectra.GroupNerveCoordinates
public import SerrePositivity.KST.Spectra.KanEquivalenceBridge
public import SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FromCategoriesToSimplicialSets.KanCharacterization
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.ContinuousKanWeakEquivalence
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.WeakWhitehead
public import Mathlib.AlgebraicTopology.SimplicialSet.NerveAdjunction

/-!
概要：群 nerve の連続 Kan 置換の高次ホモトピー消滅。
方針：StrictSegal 性から元の境界定数単体を定数と同定し、Kan 置換単位の逆で全基点へ移す。
規約：KanHomotopy の添字は実次数。群の可換性や有限性は不要。
使われ方：Sp-8 (2)、K-cof が使う n > 1 の消滅。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.KST.LocalizingInvariants.CoreFlag
open InfinityCategories Spectra

/-- 元の Kan 複体で全基点に成り立つ消滅は、連続 Kan 置換の任意の基点にも成り立つ。 -/
lemma continuousKanReplacement_kanHomotopy_subsingleton (X : SSet.{u}) [KanComplex X]
    (n : ℕ) (hX : ∀ x : X _⦋0⦌, Subsingleton (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy X n x))
    (y : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.obj X) _⦋0⦌) :
    Subsingleton (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.obj X) n y) := by
  have : KanComplex ((𝟭 SSet.{u}).obj X) := inferInstanceAs (KanComplex X)
  have : Quasicategory ((𝟭 SSet.{u}).obj X) := inferInstanceAs (Quasicategory X)
  have hu : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app X) := by
    have hw := _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.continuousKanReplacementUnit_isWeakHomotopyEquivalence X
    exact hw.isSimplicialHomotopyEquivalence.isQCatEquivalence
  obtain ⟨r, hr, hs⟩ := hu
  have he : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence r := ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app X, hs, hr⟩
  have hπ := kanPiIsomorphism_of_qCatEquivalence r he
  have : Subsingleton (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy ((𝟭 SSet.{u}).obj X) n (r.app _ y)) := hX (r.app _ y)
  exact Function.Injective.subsingleton (hπ y n).injective

/-- 群の一対象圏の nerve の連続 Kan 置換では、実次数 n > 1 の全ホモトピー類が一意。 -/
lemma groupNerve_continuousKanReplacement_kanHomotopy_subsingleton
    (G : Type u) [Group G] (n : ℕ) (hn : 1 < n)
    (x : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.obj (nerve (AsSmall.{u} (SingleObj G)))) _⦋0⦌) :
    Subsingleton (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.obj (nerve (AsSmall.{u} (SingleObj G)))) n x) := by
  have : IsGroupoid (AsSmall.{u} (SingleObj G)) :=
    isGroupoid_of_reflects_iso (AsSmall.equiv (C := SingleObj G)).inverse
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FromCategoriesToSimplicialSets.groupoidNerve_kanComplex (AsSmall.{u} (SingleObj G))
  exact continuousKanReplacement_kanHomotopy_subsingleton _ n
    (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.CoreFlag.strictSegal_kanHomotopy_subsingleton _ n hn) x

end SerrePositivity.KST.LocalizingInvariants.CoreFlag
