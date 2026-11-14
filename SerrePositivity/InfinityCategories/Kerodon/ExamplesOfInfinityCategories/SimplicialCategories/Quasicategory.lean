module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.FilledRestriction
public import Mathlib.AlgebraicTopology.Quasicategory.Basic
public import Mathlib.Tactic.CrossRefAttribute

/-!
# 局所 Kan な単体的圏の coherent nerve

概要：各 Hom が Kan 複体である単体的圏の coherent nerve は quasicategory である。
方針：内部ホーンから空洞部分の写像を貼り合わせ、端点 Hom の Kan 性で延長して
豊穣関手を復元し、各面への制限を検査する。
規約：Mathlib の SimplicialNerve をそのまま用い、追加の充填仮定を導入しない。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.1（Tag 00LJ） の局所 Kan な単体的圏からの ∞ 圏化。

対応節は Kerodon 2.4（Tag 00JN）。
-/

@[expose] public section

universe v u

open CategoryTheory

namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories

/-- 概要：局所 Kan な単体的圏の Mathlib の SimplicialNerve は quasicategory である。
方針：各内部ホーンの端点 Hom の Kan 延長から豊穣関手を復元し、面ごとの充填判定を使う。
規約：前提は単体的圏と全ての豊穣 Hom の Kan 性のみ。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.1（Tag 00LJ）。γ1 の最終定理。 -/
@[kerodon 00LJ]
instance simplicialNerve_quasicategory (C : Type u) [Category.{v} C] [SimplicialCategory C]
    [∀ X Y : C, SSet.KanComplex (SimplicialCategory.sHom X Y)] :
    SSet.Quasicategory (SimplicialNerve C) := by
  apply SSet.quasicategory_of_filler
  intro n i σ h0 hn
  obtain ⟨g, hg⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornHollowHom_extension σ h0 hn
  exact ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornFilledFunctor σ h0 hn g hg, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornFilledFunctor_face σ h0 hn g hg⟩

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HTT "1.1.5.10"] _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.simplicialNerve_quasicategory
