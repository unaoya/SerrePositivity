module

public import SerrePositivity.EInfinity.ComplexLimits.DoldKanMooreChainMaps

/-!
# 同じ正規化 Hom 同型の元の最上位成分

概要：零次数は cycles の包含、正次数は項同型の後で元の全体集合成分を回収する。
方針：既存の正規化項同型と元の cycles 同型を展開する。
規約：元の標準正規化同型を別の選択へ変更しない。
使われ方：Hom 鎖写像に対する実 Γ 比較の自然性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.EInfinity.ComplexLimits
open CategoryTheory AlgebraicTopology
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open DGNerve.PinchedHom DoldKanComparison
variable {R : Type u} [CommRing R] {D : Type v} [DGCategory R D]

lemma standardNormalizationIso_zero_eval (x y : D)
    (s : ((normalizedMooreComplex (ModuleCat R)).obj (standardModule (R := R) x y)).X 0) :
    (homObject R D x y).iCycles 0 ((connectiveHomComplex_zeroIso (R := R) x y).hom
      (((standardNormalizationIso (R := R) x y).hom.f 0) s)) =
    (((standardMooreTermIso (R := R) x y 0).hom s).val).val.component
      Finset.univ 0 Finset.univ_nonempty (by simp) := by
  change ((standardMooreZeroIso (R := R) x y).hom ≫
    (connectiveHomComplex_zeroIso (R := R) x y).hom ≫ (homObject R D x y).iCycles 0) s = _
  rw [← connectiveHomComplex_zeroCyclesIso_hom_subtype]
  dsimp only [standardMooreZeroIso, Iso.trans_hom, Iso.symm_hom]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rfl

lemma standardNormalizationIso_positive_eval (x y : D) (n : ℕ)
    (s : ((normalizedMooreComplex (ModuleCat R)).obj
      (standardModule (R := R) x y)).X (n + 1)) :
    (connectiveHomComplex_positiveIso (R := R) x y n).hom
      (((standardNormalizationIso (R := R) x y).hom.f (n + 1)) s) =
    (((standardMooreTermIso (R := R) x y (n + 1)).hom s).val).val.component
      Finset.univ (-(n + 1 : ℤ)) Finset.univ_nonempty (by simp) := by
  change ((standardMoorePositiveIso (R := R) x y n).hom ≫
    (connectiveHomComplex_positiveIso (R := R) x y n).inv ≫
      (connectiveHomComplex_positiveIso (R := R) x y n).hom) s = _
  rw [Iso.inv_hom_id, Category.comp_id]
  rfl

end SerrePositivity.EInfinity.ComplexLimits
