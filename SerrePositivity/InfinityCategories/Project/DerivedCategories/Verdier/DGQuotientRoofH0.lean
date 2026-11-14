module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.DGQuotientActualRoofs
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Homotopies.DGComparisons.DGRestrictionArrowReflection

/-! # 実 roof の主導来比較式を商の H⁰ に戻す

概要：商の指定実辺から作った roof の比較式は、商の閉射の H⁰ での合成式を与える。
方針：制限代表への射の前合成則と、正規化した導来随伴による等号の反映を使う。
規約：実二単体の構成は次のモジュール。使われ方：指定辺を保った商の分数表示。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded DGQuotient SSet
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D]

/-- 商の実辺を、元の代表加群から制限代表加群への主導来射に送る。 -/
def dgQuotientEdgeDerivedMap (P : Set D) {x z : D}
    (k : Truncated.Edge (X := (truncation 2).obj (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientNerve A D P))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (⟨x⟩ : QuotientObject D P)) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (⟨z⟩ : QuotientObject D P))) :=
  (moduleToDerived A D).map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRestrictionRepresentableArrow A D
    (_root_.SerrePositivity.DifferentialGraded.DGQuotient.QuotientObject D P) (_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P)
      (x := ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) x) (z := ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) z)
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.edgeClosed k))

/-- Roof の主導来比較式は、商の H⁰ での指定三閉射の合成式を与える。 -/
lemma DGQuotientActualRoof.h0_comparison (P : Set D) {x z : D}
    (k : Truncated.Edge (X := (truncation 2).obj (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientNerve A D P))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (⟨x⟩ : QuotientObject D P)) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (⟨z⟩ : QuotientObject D P)))
    (r : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGQuotientActualRoof A D P x z (dgQuotientEdgeDerivedMap A D P k)) :
    (_root_.SerrePositivity.DifferentialGraded.toHomotopy A (_root_.SerrePositivity.DifferentialGraded.DGQuotient.QuotientObject D P)).map
        ((inclusion A D P).onClosed.map (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.edgeClosed r.denominator)) ≫
      (toHomotopy A (QuotientObject D P)).map (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.edgeClosed k) =
    (_root_.SerrePositivity.DifferentialGraded.toHomotopy A (_root_.SerrePositivity.DifferentialGraded.DGQuotient.QuotientObject D P)).map
      ((inclusion A D P).onClosed.map (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.edgeClosed r.numerator)) := by
  rw [← (_root_.SerrePositivity.DifferentialGraded.toHomotopy A (_root_.SerrePositivity.DifferentialGraded.DGQuotient.QuotientObject D P)).map_comp]
  apply (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRestrictionRepresentableArrow_derived_eq_iff A D (QuotientObject D P)
    (_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P) (x := ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) r.source)
    (z := ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) z) _ _).mp
  have h₁ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRestrictionRepresentableArrow_precomp A D (QuotientObject D P)
    (_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P) (q := ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) r.source)
    (x := ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) x) (z := ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) z)
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.edgeClosed r.denominator) (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.edgeClosed k)
  have h₂ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRestrictionRepresentableArrow_map A D (QuotientObject D P)
    (inclusion A D P) (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.edgeClosed r.numerator)
  rw [← h₁, h₂, (_root_.SerrePositivity.DifferentialGraded.moduleToDerived A D).map_comp, (_root_.SerrePositivity.DifferentialGraded.moduleToDerived A D).map_comp]
  exact r.comparison.symm

end SerrePositivity.InfinityCategories.Project.DerivedCategories
