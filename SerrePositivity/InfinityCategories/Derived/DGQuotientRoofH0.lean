module
public import SerrePositivity.InfinityCategories.Derived.DGQuotientActualRoofs
public import SerrePositivity.InfinityCategories.Derived.DGRestrictionArrowReflection

/-! # 実 roof の主導来比較式を商の H⁰ に戻す

概要：商の指定実辺から作った roof の比較式は、商の閉射の H⁰ での合成式を与える。
方針：制限代表への射の前合成則と、正規化した導来随伴による等号の反映を使う。
規約：実二単体の構成は次のモジュール。使われ方：指定辺を保った商の分数表示。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGQuotient DGNerve DGNerve.HomotopyComparison SSet
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 商の実辺を、元の代表加群から制限代表加群への主導来射に送る。 -/
def dgQuotientEdgeDerivedMap (P : Set D) {x z : D}
    (k : Truncated.Edge (X := (truncation 2).obj (dgQuotientNerve A D P))
      (Simplex.vertex (⟨x⟩ : QuotientObject D P)) (Simplex.vertex (⟨z⟩ : QuotientObject D P))) :=
  (moduleToDerived A D).map (dgRestrictionRepresentableArrow A D
    (QuotientObject D P) (inclusion A D P)
      (x := ForgetEnrichment.of (Complex A) x) (z := ForgetEnrichment.of (Complex A) z)
      (edgeClosed k))

/-- Roof の主導来比較式は、商の H⁰ での指定三閉射の合成式を与える。 -/
lemma DGQuotientActualRoof.h0_comparison (P : Set D) {x z : D}
    (k : Truncated.Edge (X := (truncation 2).obj (dgQuotientNerve A D P))
      (Simplex.vertex (⟨x⟩ : QuotientObject D P)) (Simplex.vertex (⟨z⟩ : QuotientObject D P)))
    (r : DGQuotientActualRoof A D P x z (dgQuotientEdgeDerivedMap A D P k)) :
    (toHomotopy A (QuotientObject D P)).map
        ((inclusion A D P).onClosed.map (edgeClosed r.denominator)) ≫
      (toHomotopy A (QuotientObject D P)).map (edgeClosed k) =
    (toHomotopy A (QuotientObject D P)).map
      ((inclusion A D P).onClosed.map (edgeClosed r.numerator)) := by
  rw [← (toHomotopy A (QuotientObject D P)).map_comp]
  apply (dgRestrictionRepresentableArrow_derived_eq_iff A D (QuotientObject D P)
    (inclusion A D P) (x := ForgetEnrichment.of (Complex A) r.source)
    (z := ForgetEnrichment.of (Complex A) z) _ _).mp
  have h₁ := dgRestrictionRepresentableArrow_precomp A D (QuotientObject D P)
    (inclusion A D P) (q := ForgetEnrichment.of (Complex A) r.source)
    (x := ForgetEnrichment.of (Complex A) x) (z := ForgetEnrichment.of (Complex A) z)
    (edgeClosed r.denominator) (edgeClosed k)
  have h₂ := dgRestrictionRepresentableArrow_map A D (QuotientObject D P)
    (inclusion A D P) (edgeClosed r.numerator)
  rw [← h₁, h₂, (moduleToDerived A D).map_comp, (moduleToDerived A D).map_comp]
  exact r.comparison.symm

end SerrePositivity.InfinityCategories
