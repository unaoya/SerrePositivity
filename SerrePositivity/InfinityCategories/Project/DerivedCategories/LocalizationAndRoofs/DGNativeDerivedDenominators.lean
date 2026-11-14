module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.DGQuotientClosedRoofs

/-! # 有限 cell の導来分母の元の閉 dg 射による表示

概要：表現可能対象を終点とする有限 cell 分母を、元の dg 対象からの閉射に戻す。
方針：前三角性による始域の表現と、代表加群間の導来射の全射性を使う。
規約：標的の追加射やシフトを固定しない。使われ方：全次数の相対零化と roof。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated A D]

/-- 有限 cell 分母の始域を元の対象へ戻し、導来同型と閉射を同時に回収する。 -/
theorem dgDerivedDenominator_exists_closed (P : Set D) (x : D)
    {E : DerivedModuleCategory A D} (hE : derivedFiniteCellOver A D Set.univ E)
    (s : E ⟶ (moduleToDerived A D).obj
      (ForgetEnrichment.of (Complex A) (representable A x)))
    (hs : (derivedFiniteCellOver A D P).trW s) :
    ∃ (q : D) (i : (moduleToDerived A D).obj
      (ForgetEnrichment.of (Complex A) (representable A q)) ≅ E)
      (t : ForgetEnrichment.of (Complex A) q ⟶ ForgetEnrichment.of (Complex A) x),
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRepresentableDerivedMap A D t = i.hom ≫ s ∧
        (derivedFiniteCellOver A D P).trW (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRepresentableDerivedMap A D t) := by
  obtain ⟨q, ⟨e⟩⟩ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgTria_isRepresentable A D (⟨E, hE⟩ : TriaCategory A D)
  let i := ((triaInclusion A D).mapIso e).symm
  obtain ⟨t, ht⟩ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRepresentableDerivedMap_surjective A D
    (ForgetEnrichment.of (Complex A) q) (ForgetEnrichment.of (Complex A) x) (i.hom ≫ s)
  refine ⟨q, i, t, ht, ?_⟩
  rw [ht]
  exact ((derivedFiniteCellOver A D P).trW.arrow_mk_iso_iff
    (Arrow.isoMk i.symm (Iso.refl _) (by simp))).mp hs

end SerrePositivity.InfinityCategories.Project.DerivedCategories
