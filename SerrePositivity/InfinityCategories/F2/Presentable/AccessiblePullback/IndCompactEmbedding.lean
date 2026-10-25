module

public import SerrePositivity.InfinityCategories.F2.Compact.IndCompactRetraction
public import SerrePositivity.InfinityCategories.F2.Compact.RepresentableRetractions
public import SerrePositivity.InfinityCategories.F2.Ind.NativeFilteredPreservation
public import SerrePositivity.InfinityCategories.F2.Presentable.AccessibleIndRepresentation
public import SerrePositivity.InfinityCategories.F2.Presentable.CompactEquivalence

/-!
概要：同じ濃度の accessible 圏を前層圏へ送り、compact 対象と filtered 余極限を保つ。
方針：元の Ind 同値と全 Ind 包含を合成し、compact 対象の Yoneda retract を利用する。
規約：元の圏に全小余極限の存在を追加しない。
使われ方：任意の小さい compact 前置図式の相対因子化を前層圏で行う。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback

/-- 概要：元の Ind 包含は同じ濃度の全 compact 対象を前層の compact 対象へ送る。
方針：元の compact 対象の Yoneda retract を包含で写す。
規約：濃度を拡大せず、元の retract と同じ対象を使う。
使われ方：前層内での全 compact 図式の因子化。 -/
lemma indInclusion_preservesCompact (μ : Cardinal.{u}) [Fact μ.IsRegular]
    {A : SSet.{u}} [Quasicategory A] (x : Ind.IndInfinity μ A _⦋0⦌)
    (hx : Compact.IsKappaCompact.{u, u + 1} μ x) :
    Compact.IsKappaCompact.{u, u + 1} μ ((Ind.indInclusionPresheaf μ A).app _ x) := by
  obtain ⟨a, hr⟩ := Compact.indCompact_retract_yoneda μ x hx
  have hr' := hr.map (Ind.indInclusionPresheaf μ A)
  have hy : Compact.IsKappaCompact.{u, u + 1} μ
      ((Ind.indInclusionPresheaf μ A).app _ ((Ind.indYoneda μ A).app _ (ULift.up a))) := by
    change Compact.IsKappaCompact.{u, u + 1} μ
      ((Ind.indYoneda μ A ≫ Ind.indInclusionPresheaf μ A).app _ (ULift.up a))
    rw [Ind.indYoneda_inclusion]
    exact Compact.yonedaInfinityMap_isKappaCompact μ a
  exact Compact.IsKappaCompact.of_retract hr' hy

/-- 概要：同じ μ-accessible 圏には μ-filtered 保存かつ μ-compact 保存の前層埋め込みがある。
方針：元の Ind 表示同値の逆を同じ前層包含へ合成する。
規約：全小余極限保存は仮定しない。
使われ方：元の全 compact 前置図式の周囲での余極限構成。 -/
lemma exists_presheafEmbedding {μ : Cardinal.{u}}
    {C : SSet.{u + 1}} [Quasicategory C] (hC : IsKappaAccessible μ C) :
    ∃ (A : SSet.{u}) (hA : Quasicategory A), letI := hA
      ∃ j : C ⟶ PresheafInfinity A, IsFullyFaithful j ∧ IsKappaAccessibleFunctor μ j ∧
        ∀ x, Compact.IsKappaCompact.{u, u + 1} μ x →
          Compact.IsKappaCompact.{u, u + 1} μ (j.app _ x) := by
  have : Fact μ.IsRegular := ⟨hC.1⟩
  obtain ⟨A, hA, ⟨e⟩⟩ := hC.exists_indEquivalence
  have := hA
  let j := e.inv ≫ Ind.indInclusionPresheaf μ A
  refine ⟨A, hA, j, e.symm.isQCatEquivalence.isFullyFaithful.comp
    (Ind.indInclusionPresheaf_isFullyFaithful μ A),
    (equivalence_preservesSmallKappaFilteredColimits μ e.symm.isQCatEquivalence).comp
      (Ind.indInclusion_preservesSmallKappaFilteredColimits μ A), ?_⟩
  intro x hx
  exact indInclusion_preservesCompact μ (e.inv.app _ x)
    ((isKappaCompact_iff_equivalence e.symm x).mp hx)

end SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback
