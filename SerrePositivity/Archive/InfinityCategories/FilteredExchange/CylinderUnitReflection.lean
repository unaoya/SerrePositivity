module

public import SerrePositivity.InfinityCategories.Project.DerivedCategories.PiCriterion.ContinuousKanUnitHomotopy

/-!
概要：両端点の直和から指定した円柱の充填を、Kan 置換前のホモトピーへ戻す。
方針：境界の厳密な等式から置換内のホモトピーを作り、単位の反映性を使う。
規約：パラメータの有限性は不要。
使われ方：同時相対検出で得られた二つの fiber 内の円柱を戻す。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 概要：置換内の指定境界の円柱から、元の Kan 対象内のホモトピーを得る。
方針：直和の両脚で端点を計算し、単位によるホモトピー反映を使う。
規約：元の二端点は厳密に保持。使われ方：積比較の単射側での同時反映。 -/
lemma continuousKanReplacementUnit_reflects_cylinder {K X : SSet.{u}} [KanComplex X]
    (s : K ⨿ K ⟶ X) (r : K ⊗ (Δ[1] : SSet.{u}) ⟶ continuousKanReplacement.obj X)
    (h : coprod.desc (SSet.ι₀ : K ⟶ K ⊗ (Δ[1] : SSet.{u})) SSet.ι₁ ≫ r =
      s ≫ continuousKanReplacementUnit.app X) :
    Nonempty (SSet.Homotopy ((coprod.inl : K ⟶ K ⨿ K) ≫ s)
      ((coprod.inr : K ⟶ K ⨿ K) ≫ s)) := by
  apply continuousKanReplacementUnit_reflects_homotopy
  refine ⟨r, ?_, ?_, ?_⟩
  · change SSet.ι₀ ≫ r = ((coprod.inl : K ⟶ K ⨿ K) ≫ s) ≫
      continuousKanReplacementUnit.app X
    have hh := congrArg (fun z ↦ (coprod.inl : K ⟶ K ⨿ K) ≫ z) h
    simpa only [← Category.assoc, coprod.inl_desc] using hh
  · change SSet.ι₁ ≫ r = ((coprod.inr : K ⟶ K ⨿ K) ≫ s) ≫
      continuousKanReplacementUnit.app X
    have hh := congrArg (fun z ↦ (coprod.inr : K ⟶ K ⨿ K) ≫ z) h
    simpa only [← Category.assoc, coprod.inr_desc] using hh
  · apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro x
    exact False.elim x.1.property

end SerrePositivity.InfinityCategories.F2
