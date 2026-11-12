module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGRepresentableDerivedMaps
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGPretriangulatedTria
public import SerrePositivity.DifferentialGraded.Quotient.DerivedComparison.Equivalence

/-! # 有限 cell roof の二射を元の dg 圏へ戻す

概要：商の制限代表加群への射は、元の対象を始域とする閉 dg 射の roof で表示できる。
方針：有限 cell 始域を前三角性で表現可能に戻し、二射を Yoneda の全射性で回収する。
規約：分母の所属はこの段階では主導来圏の trW。使われ方：native 実辺への昇格。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded DGQuotient
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated A D]

/-- 有限 cell roof は、元の dg 対象からの二つの閉射で表示できる。 -/
theorem dgQuotient_exists_closedRoof (P : Set D) (hP : localKFlat A D P) (x z : D)
    (f : (moduleToDerived A D).obj (ForgetEnrichment.of (Complex A) (representable A x)) ⟶
      (moduleToDerived A D).obj
        (ForgetEnrichment.of (Complex A) (quotientRepresentableRestriction A D P z))) :
    ∃ (q : D) (s : (ForgetEnrichment.of (Complex A) q) ⟶
      (ForgetEnrichment.of (Complex A) x))
      (g : (ForgetEnrichment.of (Complex A) q) ⟶ (ForgetEnrichment.of (Complex A) z)),
      (derivedFiniteCellOver A D P).trW (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRepresentableDerivedMap A D s) ∧
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRepresentableDerivedMap A D g ≫ (moduleToDerived A D).map
        (representableRestrictionMap A D (QuotientObject D P) (inclusion A D P) z) =
          _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRepresentableDerivedMap A D s ≫ f := by
  have hx := (moduleFiniteCellOver A D Set.univ).prop_map_obj (moduleToDerived A D)
    (moduleFiniteCell_representable A D x)
  obtain ⟨E, hE, s, g, hs, hg⟩ :=
    quotientRepresentable_exists_finiteCellRoof A D P hP z hx f
  obtain ⟨q, ⟨e⟩⟩ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgTria_isRepresentable A D (⟨E, hE⟩ : TriaCategory A D)
  let i := (triaInclusion A D).mapIso e
  obtain ⟨s', hs'⟩ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRepresentableDerivedMap_surjective A D
    (ForgetEnrichment.of (Complex A) q) (ForgetEnrichment.of (Complex A) x) (i.inv ≫ s)
  obtain ⟨g', hg'⟩ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRepresentableDerivedMap_surjective A D
    (ForgetEnrichment.of (Complex A) q) (ForgetEnrichment.of (Complex A) z) (i.inv ≫ g)
  refine ⟨q, s', g', ?_, ?_⟩
  · rw [hs']
    exact ((derivedFiniteCellOver A D P).trW.arrow_mk_iso_iff
      (Arrow.isoMk i (Iso.refl _) (by simp))).mp hs
  · rw [hg', hs', Category.assoc, hg, Category.assoc]

end SerrePositivity.InfinityCategories.Project.DerivedCategories
