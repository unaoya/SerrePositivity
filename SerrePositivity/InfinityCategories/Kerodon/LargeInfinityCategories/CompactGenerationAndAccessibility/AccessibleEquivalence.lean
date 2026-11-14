module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.GeneratorEquivalence
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.AccessibleIndRepresentation
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：accessibility は同値で不変であり、小さい Ind 表現によって必要十分に判定できる。
方針：同じ小さい filtered 余極限と同じ compact 生成圏を輸送し、既存の実比較同値と合成。
規約：κ の正則性を明示。Ind 表現の結論を定義の仮定へ組み込まない。
使われ方：HTT 5.4.2、presentable ∞ 圏の特徴づけ。

対応節は Kerodon 9.4（Tag 06GT）。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility

/-- κ-accessibility は、同じ濃度・小さい生成圏を保って元の同値で輸送される。 -/
lemma IsKappaAccessible.of_equivalence {κ : Cardinal.{u}}
    {C E : SSet.{u + 1}} [Quasicategory C] [Quasicategory E]
    (h : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessible κ C) (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence C E) : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessible κ E := by
  obtain ⟨hκ, hC, A, hA, i, hi⟩ := h
  have := hA
  exact ⟨hκ, _root_.SerrePositivity.InfinityCategories.HTT.AccessibleInfinityCategories.hasSmallKappaFilteredColimits_of_equivalence e hC,
    A, hA, i ≫ e.hom, hi.of_equivalence e⟩

/-- 元の同値は、同じ濃度についての κ-accessibility を保存・反映する。 -/
lemma isKappaAccessible_iff_equivalence {κ : Cardinal.{u}}
    {C E : SSet.{u + 1}} [Quasicategory C] [Quasicategory E] (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence C E) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessible κ C ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessible κ E :=
  ⟨fun h ↦ h.of_equivalence e, fun h ↦ h.of_equivalence e.symm⟩

/-- accessibility は元の全 ∞ 圏同値で不変。 -/
lemma isAccessible_iff_equivalence {C E : SSet.{u + 1}}
    [Quasicategory C] [Quasicategory E] (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence C E) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsAccessible C ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsAccessible E := by
  constructor
  · rintro ⟨κ, h⟩
    exact ⟨κ, h.of_equivalence e⟩
  · rintro ⟨κ, h⟩
    exact ⟨κ, h.of_equivalence e.symm⟩

/-- κ-accessibility は、正則 κ と小さい ∞ 圏の Indκ との同値の存在に必要十分。 -/
@[kerodon 06K6]
lemma isKappaAccessible_iff_indEquivalence (κ : Cardinal.{u})
    (C : SSet.{u + 1}) [Quasicategory C] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessible κ C ↔ κ.IsRegular ∧
      ∃ (A : SSet.{u}) (hA : Quasicategory A),
        letI := hA
        Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndInfinity κ A) C) := by
  constructor
  · intro h
    exact ⟨h.1, h.exists_indEquivalence⟩
  · rintro ⟨hκ, A, hA, ⟨e⟩⟩
    have := hA
    have : Fact κ.IsRegular := ⟨hκ⟩
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indInfinity_isKappaAccessible κ A).of_equivalence e

/-- accessibility は、ある正則 κ と小さい ∞ 圏の Indκ との同値の存在に必要十分。 -/
lemma isAccessible_iff_indEquivalence (C : SSet.{u + 1}) [Quasicategory C] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsAccessible C ↔ ∃ κ : Cardinal.{u}, κ.IsRegular ∧
      ∃ (A : SSet.{u}) (hA : Quasicategory A),
        letI := hA
        Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndInfinity κ A) C) :=
  exists_congr (fun κ ↦ isKappaAccessible_iff_indEquivalence κ C)

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HTT "5.4.2.1"] _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.isKappaAccessible_iff_indEquivalence
attribute [cite HTT "5.4.2.2"] _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.isKappaAccessible_iff_indEquivalence
attribute [cite HTT "5.4.5.1" (partial := special) "仮定：accessible な C と終対象 x の一点図式（Lean が強い：任意の小図式 p ではなく終対象の一点）。結論：元の C/x は C への同じ射影が trivial Kan fibration、従って全準圏同値となるので accessible（この場合に一致）。同値模型を新しく仮定するのでなく終対象の既存判定から構成する。"] _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.isAccessible_iff_equivalence
attribute [cite HTT "5.4.5.15" (partial := special) "仮定：τ-accessible な C と τ-compact な始対象 x の一点図式（Lean が強い：一般の κ-small compact 図式を始対象の一点に限定）。結論：同じ Cx/ は C への射影が全準圏同値なので τ-accessible、かつ元の余錐の τ-compact 性は射影頂点の τ-compact 性と同値（この場合に両結論が一致）。"] _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.isKappaAccessible_iff_equivalence
attribute [cite HTT "5.4.5.16" (partial := special) "仮定：accessible な C と始対象 x の一点図式（Lean が強い）。結論：元の Cx/ の射影は終始対象の境界判定から trivial Kan fibration であり、C と全同値なので accessible（この場合に一致）。一般の小図式の下圏の生成性を結論したとは数えない。"] _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.isAccessible_iff_equivalence
attribute [cite HTT "5.4.6.7" (partial := special) "仮定：accessible な C と終対象 x の一点図式（Lean が強い：p を終対象の一点に限定）。結論：同じ C/x は実際の射影によって C と全準圏同値、従って accessible（この場合に一致）。元の全 Hom と高次単体を保つ同値であり、通常圏の上圏への置換ではない。"] _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.isAccessible_iff_equivalence
