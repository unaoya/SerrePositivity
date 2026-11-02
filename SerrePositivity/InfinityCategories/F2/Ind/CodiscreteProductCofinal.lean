module

public import SerrePositivity.InfinityCategories.F2.Ind.CodiscreteConeLabels
public import SerrePositivity.InfinityCategories.Core.Filtered.FilteredEquivalence
public import SerrePositivity.InfinityCategories.F1B.Cofinality.TrivialFibrationCofinality

/-!
概要：非空の codiscrete ラベルを付ける積の射影は cofinal で、κ-filtered 性を保ち反映する。
方針：ラベル写像の境界延長で同じ射影を trivial Kan fibration とし、既存の cofinality と同値不変性を使う。
規約：元の積の射影そのものを使い、余分な同値性を仮定しない。
使われ方：小さい部分複体に未使用頂点を加えるための底の cofinal な置き換え。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable (C : SSet.{u}) (T : Type u) [Nonempty T]

/-- ラベル付き積の元の射影は、ラベルの境界延長によって全境界を持ち上げる。 -/
instance codiscreteProductProjection_trivialKanFibration :
    TrivialKanFibration (fst C (nerve (Codiscrete T))) := by
  apply (trivialKanFibration_iff_boundary _).2
  intro n
  constructor
  intro a b sq
  obtain ⟨g, hg⟩ := codiscreteNerve_exists_extension (boundary n).ι
    (a ≫ snd C (nerve (Codiscrete T)))
  refine CommSq.HasLift.mk' { l := lift b g, fac_left := ?_, fac_right := by simp }
  apply CartesianMonoidalCategory.hom_ext
  · simpa only [Category.assoc, lift_fst] using sq.w.symm
  · simpa only [Category.assoc, lift_snd] using hg

/-- 非空のラベルを付けた積の元の射影は right cofinal。 -/
lemma codiscreteProductProjection_isRightCofinal :
    IsRightCofinal (fst C (nerve (Codiscrete T))) :=
  isRightCofinal_of_trivialKanFibration _

/-- 同じラベル付き積は、元の底が quasicategory なら quasicategory。 -/
instance codiscreteProduct_quasicategory [Quasicategory C] :
    Quasicategory (C ⊗ nerve (Codiscrete T)) :=
  quasicategory_of_innerFibration (fst C (nerve (Codiscrete T)))

/-- 同じ積の元の射影の ∞ 同値性は、元の κ-filtered 性を保ち反映する。 -/
lemma isKappaFiltered_codiscreteProduct_iff [Quasicategory C] (κ : Cardinal.{u}) :
    IsKappaFiltered κ (C ⊗ nerve (Codiscrete T)) ↔ IsKappaFiltered κ C := by
  have he := isQCatEquivalence_of_trivialKanFibration (fst C (nerve (Codiscrete T)))
  exact isKappaFiltered_iff_of_isQCatEquivalence he

end SerrePositivity.InfinityCategories.F2.Ind
