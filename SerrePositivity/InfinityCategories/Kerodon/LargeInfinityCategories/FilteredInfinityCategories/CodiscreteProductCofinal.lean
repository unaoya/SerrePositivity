module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.CodiscreteConeLabels
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.FilteredEquivalence
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.TrivialFibrationCofinality

/-!
概要：非空の codiscrete ラベルを付ける積の射影は cofinal で、κ-filtered 性を保ち反映する。
方針：ラベル写像の境界延長で同じ射影を trivial Kan fibration とし、既存の cofinality と同値不変性を使う。
規約：元の積の射影そのものを使い、余分な同値性を仮定しない。
使われ方：小さい部分複体に未使用頂点を加えるための底の cofinal な置き換え。

対応節は Kerodon 9.1（Tag 05WY）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories
variable (C : SSet.{u}) (T : Type u) [Nonempty T]

/-- ラベル付き積の元の射影は、ラベルの境界延長によって全境界を持ち上げる。 -/
instance codiscreteProductProjection_trivialKanFibration :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (fst C (nerve (Codiscrete T))) := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.trivialKanFibration_iff_boundary _).2
  intro n
  constructor
  intro a b sq
  obtain ⟨g, hg⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.codiscreteNerve_exists_extension (boundary n).ι
    (a ≫ snd C (nerve (Codiscrete T)))
  refine CommSq.HasLift.mk' { l := lift b g, fac_left := ?_, fac_right := by simp }
  apply CartesianMonoidalCategory.hom_ext
  · simpa only [Category.assoc, lift_fst] using sq.w.symm
  · simpa only [Category.assoc, lift_snd] using hg

/-- 非空のラベルを付けた積の元の射影は right cofinal。 -/
lemma codiscreteProductProjection_isRightCofinal :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsRightCofinal (fst C (nerve (Codiscrete T))) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.isRightCofinal_of_trivialKanFibration _

/-- 同じラベル付き積は、元の底が quasicategory なら quasicategory。 -/
instance codiscreteProduct_quasicategory [Quasicategory C] :
    Quasicategory (C ⊗ nerve (Codiscrete T)) :=
  quasicategory_of_innerFibration (fst C (nerve (Codiscrete T)))

/-- 同じ積の元の射影の ∞ 同値性は、元の κ-filtered 性を保ち反映する。 -/
lemma isKappaFiltered_codiscreteProduct_iff [Quasicategory C] (κ : Cardinal.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsKappaFiltered κ (C ⊗ nerve (Codiscrete T)) ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsKappaFiltered κ C := by
  have he := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isQCatEquivalence_of_trivialKanFibration (fst C (nerve (Codiscrete T)))
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.isKappaFiltered_iff_of_isQCatEquivalence he

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories
