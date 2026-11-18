module

public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.DoldKanHomChainMaps

/-!
# 実 smart 切断の零・正次数と同じ Hom 鎖写像

概要：切断の元の射は cycles の包含・正次数の項同型と可換である。
方針：Mathlib の実 truncLE'Map の各成分公式を適用する。
規約：同じ Hom 鎖写像と元の smart 切断を使う。
使われ方：標準正規化と実 Γ の Hom 鎖写像への自然性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.ComplexLimits
open _root_.CategoryTheory _root_.HomologicalComplex
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.InfinityCategories

variable {R : Type u} [CommRing R] {D E : Type v} [DGCategory R D] [DGCategory R E]
  {x y : D} {x' y' : E}

lemma connectiveHomComplex_zero_chainMap
    (f : homObject R D x y ⟶ homObject R E x' y') :
    (truncLE'Map f (ComplexShape.embeddingUpIntLE 0)).f 0 ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.connectiveHomComplex_zeroIso (R := R) x' y').hom ≫ (homObject R E x' y').iCycles 0 =
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.connectiveHomComplex_zeroIso (R := R) x y).hom ≫ (homObject R D x y).iCycles 0 ≫ f.f 0 := by
  have hb : (ComplexShape.embeddingUpIntLE 0).BoundaryLE 0 :=
    (ComplexShape.boundaryLE_embeddingUpIntLE_iff 0 0).mpr rfl
  rw [truncLE'Map_f_eq_cyclesMap f _ hb
    (show (ComplexShape.embeddingUpIntLE 0).f 0 = (0 : ℤ) by simp)]
  change ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.connectiveHomComplex_zeroIso (R := R) x y).hom ≫ cyclesMap f 0 ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.connectiveHomComplex_zeroIso (R := R) x' y').inv) ≫ _ = _
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [cyclesMap_i]

lemma connectiveHomComplex_positive_chainMap
    (f : homObject R D x y ⟶ homObject R E x' y') (n : ℕ) :
    (truncLE'Map f (ComplexShape.embeddingUpIntLE 0)).f (n + 1) ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.connectiveHomComplex_positiveIso (R := R) x' y' n).hom =
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.connectiveHomComplex_positiveIso (R := R) x y n).hom ≫ f.f (-(n + 1 : ℤ)) := by
  have hb : ¬ (ComplexShape.embeddingUpIntLE 0).BoundaryLE (n + 1) := by
    rw [ComplexShape.boundaryLE_embeddingUpIntLE_iff]
    omega
  rw [truncLE'Map_f_eq f _ hb
    (show (ComplexShape.embeddingUpIntLE 0).f (n + 1) = -(n + 1 : ℤ) by simp)]
  change ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.connectiveHomComplex_positiveIso (R := R) x y n).hom ≫ f.f (-(n + 1 : ℤ)) ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.connectiveHomComplex_positiveIso (R := R) x' y' n).inv) ≫ _ = _
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

end SerrePositivity.ComplexLimits
