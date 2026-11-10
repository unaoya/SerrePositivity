module

public import SerrePositivity.InfinityCategories.F2.Presentable.GeneratorEquivalence
public import SerrePositivity.InfinityCategories.F2.Presentable.AccessibleIndRepresentation
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：accessibility は同値で不変であり、小さい Ind 表現によって必要十分に判定できる。
方針：同じ小さい filtered 余極限と同じ compact 生成圏を輸送し、既存の実比較同値と合成。
規約：κ の正則性を明示。Ind 表現の結論を定義の仮定へ組み込まない。
使われ方：HTT 5.4.2、presentable ∞ 圏の特徴づけ。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.F2.Presentable

/-- κ-accessibility は、同じ濃度・小さい生成圏を保って元の同値で輸送される。 -/
lemma IsKappaAccessible.of_equivalence {κ : Cardinal.{u}}
    {C E : SSet.{u + 1}} [Quasicategory C] [Quasicategory E]
    (h : IsKappaAccessible κ C) (e : QCatEquivalence C E) : IsKappaAccessible κ E := by
  obtain ⟨hκ, hC, A, hA, i, hi⟩ := h
  have := hA
  exact ⟨hκ, hasSmallKappaFilteredColimits_of_equivalence e hC,
    A, hA, i ≫ e.hom, hi.of_equivalence e⟩

/-- 元の同値は、同じ濃度についての κ-accessibility を保存・反映する。 -/
lemma isKappaAccessible_iff_equivalence {κ : Cardinal.{u}}
    {C E : SSet.{u + 1}} [Quasicategory C] [Quasicategory E] (e : QCatEquivalence C E) :
    IsKappaAccessible κ C ↔ IsKappaAccessible κ E :=
  ⟨fun h ↦ h.of_equivalence e, fun h ↦ h.of_equivalence e.symm⟩

/-- accessibility は元の全 ∞ 圏同値で不変。 -/
lemma isAccessible_iff_equivalence {C E : SSet.{u + 1}}
    [Quasicategory C] [Quasicategory E] (e : QCatEquivalence C E) :
    IsAccessible C ↔ IsAccessible E := by
  constructor
  · rintro ⟨κ, h⟩
    exact ⟨κ, h.of_equivalence e⟩
  · rintro ⟨κ, h⟩
    exact ⟨κ, h.of_equivalence e.symm⟩

/-- κ-accessibility は、正則 κ と小さい ∞ 圏の Indκ との同値の存在に必要十分。 -/
@[kerodon 06K6]
lemma isKappaAccessible_iff_indEquivalence (κ : Cardinal.{u})
    (C : SSet.{u + 1}) [Quasicategory C] :
    IsKappaAccessible κ C ↔ κ.IsRegular ∧
      ∃ (A : SSet.{u}) (hA : Quasicategory A),
        letI := hA
        Nonempty (QCatEquivalence (Ind.IndInfinity κ A) C) := by
  constructor
  · intro h
    exact ⟨h.1, h.exists_indEquivalence⟩
  · rintro ⟨hκ, A, hA, ⟨e⟩⟩
    have := hA
    have : Fact κ.IsRegular := ⟨hκ⟩
    exact (indInfinity_isKappaAccessible κ A).of_equivalence e

/-- accessibility は、ある正則 κ と小さい ∞ 圏の Indκ との同値の存在に必要十分。 -/
lemma isAccessible_iff_indEquivalence (C : SSet.{u + 1}) [Quasicategory C] :
    IsAccessible C ↔ ∃ κ : Cardinal.{u}, κ.IsRegular ∧
      ∃ (A : SSet.{u}) (hA : Quasicategory A),
        letI := hA
        Nonempty (QCatEquivalence (Ind.IndInfinity κ A) C) :=
  exists_congr (fun κ ↦ isKappaAccessible_iff_indEquivalence κ C)

end SerrePositivity.InfinityCategories.F2.Presentable
