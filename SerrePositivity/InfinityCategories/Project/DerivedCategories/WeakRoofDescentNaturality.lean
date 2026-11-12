module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.WeakHomotopyDescent

/-! # 二つの弱同値に沿う屋根降下の自然性

概要：屋根図式の間の可換な写像は、Kan 標的への降下とホモトピーまで可換。
方針：固定 Hom 包含と屋根比較の弱同値で、順にホモトピーを反映する。
規約：中間の屋根全空間は Kan でなくてよい。使われ方：任意標的への Hom 延長の自然性。
-/
@[expose] public section
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory MonoidalClosed SSet

/-- 可換な屋根図式の写像は、その Kan 標的への降下とホモトピーまで可換。 -/
lemma weakRoofDescent_naturality {R Q E E' Z Z' : SSet.{u}} [KanComplex Z']
    {w : R ⟶ Q} {i : Z ⟶ E} {i' : Z' ⟶ E'}
    (hw : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence w) (hi : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence i)
    (t : R ⟶ E) (t' : R ⟶ E') (m : E ⟶ E') (n : Z ⟶ Z')
    (hm : i ≫ m = n ≫ i') (ht : t ≫ m = t')
    (r : E ⟶ Z) (r' : E' ⟶ Z') (q : Q ⟶ Z) (q' : Q ⟶ Z')
    (H : SSet.Homotopy (i ≫ r) (𝟙 Z)) (H' : SSet.Homotopy (i' ≫ r') (𝟙 Z'))
    (K : SSet.Homotopy (w ≫ q) (t ≫ r))
    (K' : SSet.Homotopy (w ≫ q') (t' ≫ r')) :
    Nonempty (SSet.Homotopy (q ≫ n) q') := by
  have hr : Nonempty (SSet.Homotopy (r ≫ n) (m ≫ r')) := by
    apply (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex_piZero_eq_iff_homotopy _ _).mp
    apply (hi Z').injective
    have h₁ := (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex_piZero_eq_iff_homotopy _ _).mpr
      ⟨_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp H n⟩
    have h₂ := (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex_piZero_eq_iff_homotopy _ _).mpr
      ⟨_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp H' n⟩
    simp only [Category.assoc, Category.id_comp, Category.comp_id] at h₁ h₂
    change SSet.π₀.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (i ≫ (r ≫ n))) =
      SSet.π₀.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (i ≫ (m ≫ r')))
    rw [← Category.assoc i m, hm, Category.assoc]
    exact h₁.trans h₂.symm
  obtain ⟨Hr⟩ := hr
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex_piZero_eq_iff_homotopy _ _).mp
  apply (hw Z').injective
  have h₁ := (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex_piZero_eq_iff_homotopy _ _).mpr
    ⟨_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp K n⟩
  have h₂ := (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex_piZero_eq_iff_homotopy _ _).mpr
    ⟨_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp Hr t⟩
  have h₃ := (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex_piZero_eq_iff_homotopy _ _).mpr ⟨K'⟩
  simp only [Category.assoc] at h₁ h₂ h₃
  rw [← Category.assoc t m, ht] at h₂
  exact h₁.trans (h₂.trans h₃.symm)

end SerrePositivity.InfinityCategories.Project.DerivedCategories
